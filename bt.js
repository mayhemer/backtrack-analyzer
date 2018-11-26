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
function LCS(s1, s2, compare) {
  let result = [];
  for (let i = 0; i <= s1.length; i++) {
    result.push([]);
    for (let j = 0; j <= s2.length; j++) {
      let currValue = 0;
      if (i == 0 || j == 0) {
        currValue = 0;
      } else if (compare(s1[i - 1], s2[j - 1])) {
        currValue = result[i - 1][j - 1] + 1;
      } else {
        currValue = Math.max(result[i][j - 1], result[i - 1][j]);
      }
      result[i].push(currValue);
    }
  }

  let i = s1.length;
  let j = s2.length;

  while (result[i][j] > 0) {
    if (compare(s1[i - 1], s2[j - 1]) && (result[i - 1][j - 1] + 1 == result[i][j])) {
      s1[i - 1].equals = s2[j - 1];
      i = i - 1;
      j = j - 1;
    } else if (result[i - 1][j] > result[i][j - 1])
      i = i - 1;
    else
      j = j - 1;
  }
}

let display = {
  gid: function(marker) {
    return `${marker.tid}:${marker.id}`; // assume tids are unique cross profiles...
  },

  reset: function () {
    this.elements = [];
    $("#timeline").empty();
  },

  defer: function (bt, marker, msg = "") {
    let element = this.elements[this.gid(marker)];
    if (!element) {
      let thread = bt.threads[marker.tid];
      let process = thread.process;
      element = $("<pre>").text(
        `${MarkerType.$(marker.type)} "${marker.names.join("|")}"\n  ${process.name}/${thread.name}  ${msg}`
      );

      element = { element, marker };
      this.elements[this.gid(marker)] = element;
    }

    return element;
  },

  flush(single) {
    let elements = Object.values(this.elements);
    if (single) {
      elements.sort((a, b) => {
        return b.marker.time - a.marker.time;
      });
    } else {
      elements.sort((a, b) => {
        return b.order - a.order;
      });
    }

    let timeline = $("#timeline");
    for (let element of elements) {
      timeline.append(element.element);
    }
  },
};

class Backtrack {
  constructor(files, objectives, baseline = null) {
    this.objectivesSelector = objectives;
    this.baseline = baseline;

    this.objectivesSelector.on("change", (event) => {
      display.reset();
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
        display.flush(!this.baseline);
      }
    });

    files.on("change", (event) => {
      this.files = Array.from(event.target.files);
      this.consumeFiles();
    });

    files.trigger("change");
  }

  consumeFiles() {
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
    console.log("consume");
    for (let file of Array.from(files)) {
      console.log(file.file.name);
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
      console.log("no objectives found");
      return;
    }

    this.objectivesSelector.append($("<option>").attr("value", `0:0`).text("Select objective"));
    for (let obj of this.objectives) {
      obj.source = this.backtrack(obj.tid, obj.id, () => { });
      this.objectivesSelector
        .append($("<option>")
          .attr("value", `${obj.tid}:${obj.id}`)
          .text(`${obj.names.join("|")} @${obj.time}s → ${obj.source.names.join("|")} @${obj.source.time}s`)
        );
    }
    this.objectivesSelector.val(`0:0`);
  }

  baselineProfile(tid, id) {
    this.backtrack(
      tid, id,
      (bt, marker, className = "") => {
        display.defer(bt, marker).element.addClass(className);
      },
      (bt, trail, marker) => {
        bt.deferedBlockers.push({ trail, marker });
      }
    );
  }

  compareProfiles(tid, id) {
    let collector = function (bt, marker, className) {
      this.push({ marker, desc: bt.descriptor(marker), className });
    };
    let trailCollector = function (bt, trail, marker) {
      bt.assert(this.last().marker === marker);
      this.last().trail = trail;
    };

    let baselinePath = [];
    let [btid, bid] = this.baseline.objectivesSelector.val().split(":").map(id => parseInt(id));
    this.baseline.backtrack(btid, bid, collector.bind(baselinePath), trailCollector.bind(baselinePath));

    let modifiedPath = [];
    this.backtrack(tid, id, collector.bind(modifiedPath), trailCollector.bind(modifiedPath));

    // Fills |equals| property on the baselinePath array pointing to the modified path
    LCS(baselinePath, modifiedPath, (a, b) => a.desc === b.desc);

    let order = 0;
    while (baselinePath.length || modifiedPath.length) {
      let base = baselinePath[0];
      let mod = modifiedPath[0];

      let equal = base && base.equals && base.equals === mod;

      if (equal) {
        let base_prev;
        for (base_prev of baselinePath.slice(1)) {
          if (base_prev.equals) {
            break;
          }
        }
        let base_delay = base_prev ? base.marker.time - base_prev.marker.time : 0;
        let mod_prev = (base_prev && base_prev.equals) ? base_prev.equals : modifiedPath[1];
        let mod_delay = mod_prev ? mod.marker.time - mod_prev.marker.time : 0;

        let element = display.defer(this.baseline, base.marker,
          `\nbase: +${base_delay.toFixed(5)}s, modified: +${mod_delay.toFixed(5)}s, difference: ${(mod_delay - base_delay).toFixed(5)}s`);
        element.element.addClass("equal").addClass(base.className);
        element.order = --order;

        baselinePath.shift();
        modifiedPath.shift();
        continue;
      }

      if (base && !base.equals) {
        let base_prev = baselinePath[1] || null;
        let base_delay = base_prev ? base.marker.time - base_prev.marker.time : 0;

        let element = display.defer(this.baseline, base.marker,
          `\nbase: +${base_delay.toFixed(5)}s`);
        element.element.addClass("base").addClass(base.className);
        element.order = --order;

        baselinePath.shift();
        continue;
      }

      if (!base || (base && base.equals && base.equals != mod)) {
        let mod_prev = modifiedPath[1] || null;
        let mod_delay = mod_prev ? mod.marker.time - mod_prev.marker.time : 0;

        let element = display.defer(this, mod.marker,
          `\nmodified: +${mod_delay.toFixed(5)}s`);
        element.element.addClass("mod").addClass(mod.className);
        element.order = --order;

        modifiedPath.shift();
        continue;
      }

      throw "Impossible!";
    }
  }

  assert(cond, msg) {
    if (!cond) {
      throw msg || "Assertion failure";
    }
  }

  descriptor(marker) {
    let thread = this.threads[marker.tid];
    let process = thread.process;
    let threadName = thread.name.split('#')[0];
    return `${marker.type}@${marker.names.join("|")}@${process.type}@${threadName}`;
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
        display.defer(this, execute_begin).element
          .addClass("blocker clickable")
          .click(() => {
            let last = null;
            display.defer(this, execute_end).element.addClass("blocker trail");
            this.backtrack(execute_begin.tid, execute_begin.id, (bt, marker, className = "") => {
              last = display.defer(this, marker).element.addClass("blocker trail").addClass(className);
            });
            if (last) {
              last.addClass("join");
            }
            display.flush();
          });
      }

      pexec_gid = execute_begin.pexec_gid;
    }
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
    display.flush();
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
