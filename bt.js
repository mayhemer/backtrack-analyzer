let MarkerType = {
  NONE:  0,
  ROOT_BEGIN:  1,
  ROOT_END:  2,
  INPUT_BEGIN:  3,
  INPUT_END:  4,
  OBJECTIVE:  5,
  DISPATCH:  6,
  REDISPATCH_BEGIN:  7,
  REDISPATCH_END:  8,
  EXECUTE_BEGIN:  9,
  EXECUTE_END:  10,
  REQUEST:  11,
  RESPONSE_BEGIN:  12,
  RESPONSE_END:  13,
  BRANCH:  14,
  SLEEP:  15,
  WAKE:  16,
  LABEL: 17,
  LOOP_BEGIN: 18,
  LOOP_END: 19,
  STARTUP: 20,

  $: function (type) {
    for (let t in this) {
      if (this[t] === type) {
        return t.toString();
      }
    }
  },
};

let MarkerField = {
  NONE:  0,
  STATIC_NAME:  1,
  DYNAMIC_NAME:  2,
  BACKTRAIL:  3,
  PREVIOUS_SEQUENTIAL_DISPATCH:  4,
  PREVIOUS_EXECUTE:  5,
  TIMING:  6,
};

const FILE_SLICE = 256 << 10;

function ensure(array, itemName, def = {}) {
  if (!(itemName in array)) {
    array[itemName] = (typeof def === "function") ? def() : def;
  }

  return array[itemName];
}

Array.prototype.last = function () {
  return this[this.length - 1];
};

// Original LCS code written by Alexis Lagante @alexishacks (github)
function LCS(s1, s2) {
  let result = [];
  for (let i = 0; i <= s1.length; i++) {
    result.push([]);
    for (let j = 0; j <= s2.length; j++) {
      let currValue = 0;
      if (i == 0 || j == 0) {
        currValue = 0;
      } else if (s1[i - 1].desc === s2[j - 1].desc) {
        currValue = result[i - 1][j - 1] + 1;
      } else {
        currValue = Math.max(result[i][j - 1], result[i - 1][j]);
      }
      result[i].push(currValue);
    }
  }

  let i = s1.length;
  let j = s2.length;

  let mapping = {};
  while (result[i][j] > 0) {
    if (s1[i - 1] === s2[j - 1] && (result[i - 1][j - 1] + 1 == result[i][j])) {
      s1[i - 1].equals = j - 1;
      i = i - 1;
      j = j - 1;
    } else if (result[i - 1][j] > result[i][j - 1])
      i = i - 1;
    else
      j = j - 1;
  }
  return mapping;
}

class Backtrack {
  constructor(files, objectives, baseline = null) {
    this.objectivesSelector = objectives;
    this.files = Array.from(files.get()[0].files);
    this.baseline = baseline;

    this.objectivesSelector.on("change", (event) => {
      $("#timeline").empty();
      this.elements = {};
      this.deferedBlockers = [];
      
      try {
        let [tid, id] = this.objectivesSelector.val().split(":").map(id => parseInt(id));
        if (this.baseline) {
          this.compareProfiles(tid, id);
        } else {
          this.baselineProfile(tid, id);
        }
      } catch (ex) {
        throw ex;
      } finally {
        this.flushDisplay();
      }
    });

    files.on("change", (event) => {
      $("#timeline").empty();
      this.consumeFiles();
    });

    this.consumeFiles();
  }

  consumeFiles() {
    this.elements = {};
    this.deferedBlockers = [];

    this.objectives = [];
    this.processes = {};
    this.threads = {};

    let files = [];
    for (let file of this.files) {
      files.push(this.readFile(file));
    }

    Promise.all(files).then((files) => {
      this.consume(files);
    });
  }

  readFile(file, from = 0, line = 0, chunk = FILE_SLICE) {
    let previousLine = "";
    let halfCRLF = false;
    let slice = (segmentoffset) => {
      return new Promise((resolve, reject) => {
        let blob = file.slice(segmentoffset, segmentoffset + chunk);
        if (blob.size == 0) {
          resolve({
            file: file,
            fromline: line,
            lines: [previousLine]
          });
          return;
        }

        let reader = new FileReader();
        reader.onloadend = (event) => {
          if (event.target.readyState == FileReader.DONE && event.target.result) {
            // Change chunk size to 5MB and Chrome self-time of shift() is 1000x slower!
            let maybeDeleteFirstEmptyLine =
              halfCRLF && event.target.result.match(/^\n/);
            halfCRLF = event.target.result.match(/\r$/);

            let lines = event.target.result.split(/\r\n|\r|\n/);
            if (maybeDeleteFirstEmptyLine) {
              lines.shift();
            }

            // This simple code assumes that a single line can't be longer than FILE_SLICE
            lines[0] = previousLine + lines[0];
            previousLine = lines.pop();

            resolve({
              file: file,
              lines: lines,
              fromline: line,
              read_more: () => slice(segmentoffset + chunk)
            });
          }
        };

        reader.onerror = (event) => {
          console.error(`Error while reading at offset ${segmentoffset} from ${file.name}`);
          console.exception(reader.error);
          window.onerror(reader.error);

          reader.abort();
          reject(reader.error);
        };

        reader.readAsBinaryString(blob);
      });
    };

    return slice(from);
  }

  async consume(files) {
    for (let file of Array.from(files)) {
      let pid = file.file.name.split(".")[0];
      let process = {
        pid,
        name: pid,
      };
      this.processes[process.pid] = process;
      while (true) {
        if (!file.lines.length) {
          if (!file.read_more) {
            break;
          }

          file = await file.read_more();
        }

        let line = file.lines.shift();

        if (line) {
          this.processLine(line, process);
        }
      }
    }

    this.listObjectives();
  }

  processLine(line, process) {
    let match = line.match(/^([^:]+):([^:]+):(.*)$/);
    if (!match) {
      throw "match error";
    }

    let tid = parseInt(match[1]);
    let id = match[2];
    line = match[3];
    match = line.match(/^([^;]*)(?:;[^;]+)?$/)[1].split(":");

    let new_thread = (tid) => {
      return {
        tid,
        process,
        last: null,
        markers: [],
        rooting: [false],
        addmarker: function (id, marker) {
          if (this.last && id == 1) {
            throw "Two threads with the same id!";
          }
          marker.id = parseInt(id);
          marker.names = [];
          marker.rooted = this.rooted();

          this.last = marker;
          this.markers.push(this.last);
          if (marker.id !== this.markers.length) {
            throw "Missing marker? " + marker.id + " " + this.markers.length;
          }

          switch (marker.type) {
            case undefined:
              throw "No marker type?";
            case MarkerType.STARTUP:
            case MarkerType.EXECUTE_BEGIN:
            case MarkerType.RESPONSE_BEGIN:
            case MarkerType.REDISPATCH_BEGIN:
            case MarkerType.INPUT_BEGIN:
            case MarkerType.ROOT_BEGIN:
              this.rooting.push(true);
              break;
            case MarkerType.LOOP_BEGIN:
              this.rooting.push(false);
              break;
            case MarkerType.STARTUP:
            case MarkerType.EXECUTE_BEGIN:
            case MarkerType.RESPONSE_BEGIN:
            case MarkerType.REDISPATCH_BEGIN:
            case MarkerType.INPUT_BEGIN:
            case MarkerType.ROOT_BEGIN:
              this.assert(this.rooting.pop() === true);
              break;
            case MarkerType.LOOP_BEGIN:
              this.assert(this.rooting.pop() === false);
              break;
          }
        },
        rooted: function () {
          return this.rooting[0] === true;
        },
      }
    };

    let thread = ensure(this.threads, tid, () => new_thread(tid));

    if (id === "NT") {
      thread.name = match[0];
      if (!thread.time) {
        thread.time = match[1];
      }
    } else if (id === "NP") {
      process.name = `${match[0]}(${process.pid})`;
      process.type = match[0];
    } else  if (id == 0) { // Amend<>
      let type = parseInt(match[0]);
      switch (type) {
        case MarkerField.STATIC_NAME:
        case MarkerField.DYNAMIC_NAME:
          thread.last.names.push(match.slice(1).join(":"));
          break;
        case MarkerField.PREVIOUS_SEQUENTIAL_DISPATCH:
          thread.last.pdisp_gid = {
            tid: parseInt(match[1]),
            id: parseInt(match[2])
          };
          break;
        case MarkerField.PREVIOUS_EXECUTE:
          thread.last.pexec_gid = {
            tid: parseInt(match[1]),
            id: parseInt(match[2])
          };
          break;
      }
    } else { // Mark<>
      id = parseInt(id);
      let type = parseInt(match[0]);
      switch (type) {
        case MarkerType.OBJECTIVE:
          thread.addmarker(id, {
            tid,
            type,
            time: parseFloat(match[1]),
          });
          this.objectives.push(thread.last);
          break;
        case MarkerType.STARTUP:
          thread.addmarker(id, {
            tid,
            type,
            time: parseFloat(match[1]),
          });
          break;
        case MarkerType.DISPATCH:
        case MarkerType.REQUEST:
        case MarkerType.ROOT_BEGIN:
        case MarkerType.INPUT_BEGIN:
        case MarkerType.REDISPATCH_BEGIN:
        case MarkerType.EXECUTE_BEGIN:
        case MarkerType.RESPONSE_BEGIN:
        case MarkerType.LOOP_BEGIN:
        case MarkerType.ROOT_END:
        case MarkerType.INPUT_END:
        case MarkerType.REDISPATCH_END:
        case MarkerType.EXECUTE_END:
        case MarkerType.RESPONSE_END:
        case MarkerType.LOOP_END:
          thread.addmarker(id, {
            tid,
            type,
            time: parseFloat(match[1]),
            backtrail: {
              tid: parseInt(match[2]),
              id: parseInt(match[3])
            }
          });
          break;
      }
    }
  }

  listObjectives() {
    this.objectivesSelector.empty();
    if (!this.objectives.length) {
      return;
    }

    this.objectivesSelector.append($("<option>").attr("value", `0:0`).text("Select objective"));
    for (let obj of this.objectives) {
      let source = this.backtrack(obj.tid, obj.id, () => { });
      this.objectivesSelector
        .append($("<option>")
          .attr("value", `${obj.tid}:${obj.id}`)
          .text(`${obj.names.join("|")} @${obj.time}s → ${source.names.join("|")} @${source.time}s`)
        );
    }
    this.objectivesSelector.val(`0:0`);
  }

  baselineProfile(tid, id) {
    this.backtrack(
      tid, id,
      (bt, marker, _class = "") => {
        bt.display(marker).addClass(_class);
      },
      (bt, trail, marker) => {
        bt.deferedBlockers.push({ trail, marker });
      }
    );
  }

  compareProfiles(tid, id) {
    let collector = function (bt, marker) {
      this.push({ marker, desc: this.descriptor(marker), });
    };
    let trailCollector = function (bt, trail, marker) {
      this.last().trail = trail;
    };

    let baselinePath = [];
    this.basline.backtrack(tid, id, collector.bind(baselinePath), trailCollector.bind(baselinePath));

    let modifiedPath = [];
    this.backtrack(tid, id, collector.bind(modifiedPath), trailCollector.bind(modifiedPath));

    let mapping = LCS(baselinePath, modifiedPath);
  }

  flushDisplay() {
    let timeline = $("#timeline");
    let elements = Object.values(this.elements).sort((a, b) => {
      return b.marker.time - a.marker.time;
    });
    for (let element of elements) {
      timeline.append(element.element);
    }
  }

  assert(cond, msg) {
    if (!cond) {
      throw msg || "Assertion failure";
    }
  }

  gid(marker) {
    return `${marker.tid}:${marker.id}`;
  }

  descriptor(marker) {
    let thread = this.threads[marker.tid];
    let process = thread.process;
    return `${marker.type}/${marker.names.join("|")}/${process.type}/${thread.name}`;
  }

  get(gid) {
    let index = gid.id - 1; // we count from 1...
    this.assert(index > 0);
    return this.threads[gid.tid].markers[index];
  }

  prev(marker) {
    let index = marker.id - 1; // we count from 1...
    this.assert(index > 0, "No more markers to go back on a thread");
    return this.threads[marker.tid].markers[index - 1];
  }

  backtrail(marker) {
    this.assert(marker.backtrail, "Expected backtrail");
    this.assert(marker.backtrail.id, "Expected valid backtrail");
    let index = marker.backtrail.id - 1; // we count from 1...
    let trail = this.threads[marker.backtrail.tid].markers[index];
    switch (marker.type) {
      case MarkerType.REDISPATCH_END:
      case MarkerType.EXECUTE_END:
      case MarkerType.RESPONSE_END:
      case MarkerType.ROOT_END:
      case MarkerType.INPUT_END:
      case MarkerType.LOOP_END:
        this.assert(
          trail.type == marker.type - 1,
          "Expected *_BEGIN marker"
        );
        break;
      case MarkerType.REDISPATCH_BEGIN:
      case MarkerType.EXECUTE_BEGIN:
        this.assert(
          trail.type == MarkerType.DISPATCH ||
          trail.type == MarkerType.REDISPATCH_END ||
          trail.type == MarkerType.EXECUTE_END ||
          "Expected DISPATCH or *_END marker"
        );
        break;
      case MarkerType.RESPONSE_BEGIN:
        this.assert(
          trail.type == MarkerType.REQUEST ||
          trail.type == MarkerType.RESPONSE_END,
          "Expected REQUEST or *_END marker"
        );
        break;
    }
    return trail;
  }

  forwardtrail(source) {
    let gid = {
      tid: source.tid,
      id: source.id,
    };
    let at = Object.assign({}, gid);

    let trail;
    do {
      ++at.id;
      trail = this.get(at);
      this.assert(trail);
    } while (trail && (!trail.backtrail || trail.backtrail.id !== gid.id || trail.backtrail.tid !== gid.tid));

    return trail;
  }

  displayBlockersOf(dispatch, execute_begin) {
    let pexec_gid = execute_begin.pexec_gid;
    let up_to = this.forwardtrail(execute_begin);
    while (pexec_gid && pexec_gid.id) {
      let execute_begin = this.get(pexec_gid);
      let execute_end = this.forwardtrail(execute_begin);
      if (execute_end.time > dispatch.time && (execute_end.tid !== up_to.tid || execute_end.time < up_to.time)) {
        this.display(execute_begin)
          .addClass("blocker clickable")
          .click(() => {
            let last = null;
            this.display(execute_end).addClass("blocker trail");
            this.backtrack(execute_begin.tid, execute_begin.id, (bt, marker, _class = "") => {
              last = this.display(marker).addClass("blocker trail").addClass(_class);
            });
            if (last) {
              last.addClass("join");
            }
            this.flushDisplay();
          });
      }

      pexec_gid = execute_begin.pexec_gid;
    }
  }

  display(marker, msg = "") {
    let element = this.elements[this.gid(marker)];
    if (!element) {
      let thread = this.threads[marker.tid];
      let process = thread.process;
      element = $("<pre>")
        .text(`${MarkerType.$(marker.type)} "${marker.names.join("|")}"\n  ${marker.time}s, ${process.name}/${thread.name}${msg ? ` ${msg}` : ``}`);

      this.elements[this.gid(marker)] = { element, marker };
    } else {
      element = element.element;
    }

    return element;
  }

  backtrack(tid, id, collector, blocker_trail = () => { }) {
    let marker = this.get({ tid, id });
    while (marker) {
      switch (marker.type) {
        case MarkerType.ROOT_BEGIN:
          if (marker.rooted) {
            collector(this, marker, "span");
            marker = this.prev(marker);
            break;
          } // else fall through
        case MarkerType.INPUT_BEGIN:
        case MarkerType.STARTUP:
          collector(this, marker);
          return marker;
        case MarkerType.DISPATCH:
        case MarkerType.REQUEST:
          marker = this.prev(marker);
          break;
        case MarkerType.REDISPATCH_BEGIN:
        case MarkerType.EXECUTE_BEGIN:
        case MarkerType.RESPONSE_BEGIN:
          collector(this, marker);
          let trail = this.backtrail(marker);
          blocker_trail(this, trail, marker);
          collector(this, trail);
          marker = this.prev(trail);
          break;
        case MarkerType.ROOT_END:
          // Rooting is not interesting now (lot of dead end markings only), unblock if it becomes intersting again...
          marker = this.backtrail(marker);
          marker = this.prev(marker);
          break;
        case MarkerType.REDISPATCH_END:
        case MarkerType.EXECUTE_END:
        case MarkerType.RESPONSE_END:
        case MarkerType.LOOP_END:
        case MarkerType.INPUT_END:
          collector(this, marker, "span");
          marker = this.backtrail(marker);
          collector(this, marker, "span");
          marker = this.prev(marker);
          break;
        default:
          collector(this, marker);
          marker = this.prev(marker);
          break;
      }
    };
  }

  revealBlockers() {
    for (let execute of this.deferedBlockers) {
      let { trail, marker } = execute;
      this.displayBlockersOf(trail, marker);
    }
    this.flushDisplay();
  }
}

let sets = {
  baseline: null,
  modified: null,
};

$(() => {
  $("#timeline").empty();

  sets.baseline = new Backtrack($("#files1"), $("#objectives1"));
  sets.modified = new Backtrack($("#files2"), $("#objectives2"), sets.baseline);
});
