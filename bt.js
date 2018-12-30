let MarkerType = {
  AMEND:  0,
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
  INFO: 21,

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
  TIMING: 6,
  QUEUE_NAME: 7,
};

const SHOW_BLOCKERS_IN_DIFF = false;
const SHOW_BLOCKERS_IN_SINGLE = false;
const BLOCKER_LISTING_THRESHOLD_MS = 0;
const DEPENDECY_CLICKABLE_IN_SINGLE = true;
const SHOW_DEPENDENT_PATH_FROM_EXECUTE_END = false;

const FILE_SLICE = 256 << 10;
const PREC = 2;

function ensure(array, itemName, def = {}) {
  if (!(itemName in array)) {
    array[itemName] = (typeof def === "function") ? def() : def;
  }

  return array[itemName];
}

Array.prototype.last = function () {
  return this[this.length - 1];
};
Array.prototype.remove = function (element) {
  let index = this.findIndex(e => e === element);
  if (index > -1) {
    this.splice(index, 1);
  }
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
  let merge = [];

  while (result[i][j] > 0) {
    if (compare(s1[i - 1], s2[j - 1]) && (result[i - 1][j - 1] + 1 == result[i][j])) {
      s1[i - 1].equals = s2[j - 1];
      i = i - 1;
      j = j - 1;
      merge.unshift({ base: s1[i], mod: s2[j] });
    } else if (result[i - 1][j] > result[i][j - 1]) {
      i = i - 1;
      merge.unshift({ base: s1[i], mod: undefined });
    } else {
      j = j - 1;
      merge.unshift({ base: undefined, mod: s2[j] });
    }
  }

  while (j) {
    j = j - 1;
    merge.unshift({ base: undefined, mod: s2[j] });
  }
  while (i) {
    i = i - 1;
    merge.unshift({ base: s1[i], mod: undefined });
  }

  return merge;
}

class Breadcrumb {
  constructor(target, bt) {
    this.target = target;
    this.bt = bt;
    this.reset();
  }

  reset() {
    this.history = [];
    this.rebuild();
  }

  rebuild() {
    this.target.empty();
    for (let { marker, label, indent, scroll } of this.history) {
      this.target.append(" &gt; ");
      this.target.append($("<span>").text(
        `${MarkerType.$(marker.type)} "${marker.names.join("|").split(" ")[0]}"`
      ).click(() => {
        let drop = false;
        this.history = this.history.filter((bc) => {
          return !(drop || (drop = bc.marker === marker));
        });
        display.reset();
        this.bt.baselineProfile(marker.tid, marker.id, label.tid, label.id, indent);
        display.flush();
        $(window).scrollTop(scroll);
      }));
    }
  }

  push(marker, label, indent) {
    this.history.push({ marker, label, indent, scroll: display.prevscroll() });
    this.rebuild();
  }
}

class Display {
  constructor(timeline) {
    this.timeline = timeline;
    this.reset();
  }

  reset() {
    this.defered = [];
    this.markers = {};
    this.lastScroll = $(window).scrollTop();
    this.timeline.empty();
  }

  prevscroll() {
    return this.lastScroll;
  }

  gid(marker) {
    return `${marker.tid}:${marker.id}`; // assume tids are unique cross profiles...
  }

  sub(target, marker) {
    this.defer({ element: target, marker });
    return new Display(target);
  }

  defer(element) {
    element.order = this.defered.length;
    this.defered.push(element);
    return element;
  }

  deferMarker(bt, marker, msg = "", short = false) {
    let element = this.markers[this.gid(marker)];

    let names = marker.names;
    if (!names.length) {
      // No name on EXECUTE?  Fall back to DISPATCH
      switch (marker.type) {
        case MarkerType.EXECUTE_BEGIN:
        case MarkerType.RESPONSE_BEGIN:
          names = bt.get(marker.backtrail).names;
      }
    }

    if (!element) {
      let thread = bt.threads[marker.tid];
      let process = thread.process;
      element = $("<pre>").text(
        `${MarkerType.$(marker.type)} "${names.join("|")}" @${marker.time.toFixed(PREC)}ms` +
        (short ? "" : `\n  ${process.name}/${thread.name}  `) +
        (msg ? `\n${msg}` : "")
      ).addClass(`marker-type-${MarkerType.$(marker.type).toLowerCase()}`);

      element = { element, marker };
      this.defer(element);
      this.markers[this.gid(marker)] = element;
    } else {
      element.preexisting = true;
    }

    return element;
  }

  deferDiffTimingBar(base, mod) {
    let diff = Math.floor(mod - base) / 10 * 5;
    let element = $("<div>").addClass("full-width");
    element.append($("<div>")
      .addClass("diff-progress")
      .addClass(diff > 0 ? "plus" : "minus")
      .css("width", `${Math.min(100, Math.max(0, Math.abs(diff))) / 2}%`)
      .prop("title", `The modified profile is ${diff > 0 ? "slower" : "faster"}`)
    );
    return this.defer({ element });
  }

  deferTimingBar(time) {
    time = Math.floor(time) / 10 * 5;
    let element = $("<div>").addClass("full-width");
    element.append($("<div>")
      .addClass("diff-progress single")
      .css("width", `${Math.min(100, Math.max(0, Math.abs(time)))}%`)
    );
    return this.defer({ element });
  }

  flush(sort = () => { }) {
    let elements = Object.values(this.defered);
    sort(elements);

    for (let element of elements) {
      this.timeline.append(element.element);
    }
  }
};

let display, breadcrumbs;

// This has meaning only for incomplete (partial, not gracefully closed) profile data
class PlaceholderMarker {
  constructor() {
    this.type = MarkerType.NONE;
    this.time = 0;
    this.names = ["Placeholder for non-existent"];
    this.id = 0;
    this.tid = 0;
  }
}

class Backtrack {
  constructor(files, objectives, baseline = null) {
    objectives.select2({
      dropdownAutoWidth: true,
      width: 'calc(50% - 8px)',
      matcher: (params, data) => {
        if ($.trim(params.term) === '') {
          return data;
        }
        if (typeof data.text === 'undefined') {
          return null;
        }
        if (params.stop) {
          return null;
        }
        try {
          // "TERM1\ TERM2 TERM3" will be processed as:
          // match("TERM1 TERM2") && match("TERM3")
          let terms = params.term.split(" ").reduce((result, term) => {
            if (result.last() && result.last().slice(-1) === '\\') {
              result[result.length - 1] += " " + term;
            } else {
              result.push(term);
            }
            return result;
          }, []);
          for (let term of terms) {
            if (!data.text.match(term)) {
              return null;
            }
          }
        } catch (ex) {
          params.stop = true;
          return { text: ex.message || ex };
        }
        return data;
      }
     });
    this.objectivesSelector = objectives;
    this.filesSelector = files;
    this.baseline = baseline;

    // There is always only one!
    let searchField = () => $("input.select2-search__field");
    this.objectivesSelector.on("change", (event) => {
      display.reset();
      breadcrumbs.reset();
      try {
        let [tid, id, break_tid, break_id] = this.objectivesSelector.val().split(":").map(id => parseInt(id));
        if (this.baseline) {
          this.compareProfiles(tid, id, break_tid, break_id);
        } else {
          this.baselineProfile(tid, id, break_tid, break_id);
          if (tid === 0 && id === 0) {
            this.modified.filesSelector.prop("disabled", true);
            return;
          }
          // And now, when the basline profile's objective is selected,
          // we allow loading the modified profile.
          this.modified.filesSelector.prop("disabled", false);
          if (!this.modified.objectives.length) {
            this.modified.message(`Optionally load files for the modified profile to compare to`);
          } else {
            this.modified.objectivesSelector.prop("disabled", false);
          }
        }
      } catch (ex) {
        display.defer({ element: $("<span>").text(ex.message || ex) });
        throw ex;
      } finally {
        display.flush();
      }
    }).on("select2:open", () => {
      searchField().prop("placeholder", "Search: REGEXP [SPACE REGEXP...] to list objectives matching ALL the regexp terms");
      setTimeout(function () {
        let query = localStorage["search-field"];
        if (query && query.length) {
          searchField().val(query).trigger('input');
        };
      }, 0);
    }).on('select2:closing', function() {
      localStorage["search-field"] = searchField().prop('value');
    });
    
    files.on("change", (event) => {
      this.files = Array.from(event.target.files);
      this.consumeFiles();
    });

    files.trigger("change");
  }

  message(msg) {
    this.objectivesSelector.empty().append($("<option>")
      .attr("value", `0:0:0:0`).text(msg)
    ).val("0:0:0:0");
  }

  consumeFiles() {
    performance.mark("consume-all-begin");

    this.objectives = [];
    this.processes = {};
    this.threads = {};

    if (this.files.length == 0) {
      return;
    }

    this.message(`Loading...`);

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
          try {
            this.processLine(line, process);
          } catch (ex) {
            this.message(`Error during file read: ${ex.message || ex}`);
            throw ex;
          }
        }
      }
    }

    this.cacheForwardtrail();
    this.listObjectives();

    performance.mark("consume-all-end");
    performance.measure("consume-all", "consume-all-begin", "consume-all-end");

    let entries = performance.getEntriesByType("measure");
    for (let entry of entries) {
      console.log(entry);
    }
  }

  parseTime(timeString) {
    return parseFloat(timeString) * 1000;
  }

  processLine(line, process) {
    let fullLine = line;
    
    let match = line.match(/^([^:]+):([^:]+):(.*)$/);
    if (!match) {
      return;
    }

    let tid = parseInt(match[1]);
    let id = match[2];
    
    if (isNaN(tid)) {
      if (this.last_name_amend) {
        this.last_name_amend.names.push(line.trim());
      }
      return;
    }    
      
    this.last_name_amend = undefined;

    line = match[3];
    match = line.split(":");
    if (!match) {
      return;
    }

    let bt = this;
    let new_thread = (tid) => {
      return {
        tid,
        process,
        last: null,
        markers: [],
        rooting: [false],
        addmarker: function (id, marker) {
          bt.assertNot(this.last && id == 1, "Two threads with the same id!");
          marker.id = parseInt(id);
          marker.names = [];
          marker.rooted = this.rooted();

          this.last = marker;
          this.markers.push(this.last);
          bt.assert(marker.id === this.markers.length, `Missing marker? ${marker.id}!=${this.markers.length} "${fullLine}"`);

          switch (marker.type) {
            case undefined:
              bt.assert(false, "No marker type?");
              break;
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
            case MarkerType.EXECUTE_END:
            case MarkerType.RESPONSE_END:
            case MarkerType.REDISPATCH_END:
            case MarkerType.INPUT_END:
            case MarkerType.ROOT_END:
              bt.assert(this.rooting.pop() === true);
              break;
            case MarkerType.LOOP_END:
              bt.assert(this.rooting.pop() === false);
              break;
          }
        },
        rooted: function () {
          return this.rooting.last() === true;
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
    } else  if (id == 0) { // Amend<>, backward compat, remove soon
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
        case MarkerType.AMEND:
          let field = parseInt(match[1]);
          switch (field) {
            case MarkerField.STATIC_NAME:
            case MarkerField.DYNAMIC_NAME:
              this.last_name_amend = this.get({ tid, id });
              this.last_name_amend.names.push(match.slice(2).join(":"));
              break;
            case MarkerField.PREVIOUS_SEQUENTIAL_DISPATCH:
              this.get({ tid, id }).pdisp_gid = {
                tid: parseInt(match[2]),
                id: parseInt(match[3])
              };
              break;
            case MarkerField.PREVIOUS_EXECUTE:
              this.get({ tid, id }).pexec_gid = {
                tid: parseInt(match[2]),
                id: parseInt(match[3])
              };
              break;
            case MarkerField.QUEUE_NAME:
              this.last_name_amend = this.get({ tid, id });
              this.last_name_amend.names.push(`QUEUE:[${match.slice(2).join(":")}]`);
              break;
            default:
              this.assert(false, "Missing handler for new field type");
          }
          break;
        case MarkerType.OBJECTIVE:
          thread.addmarker(id, {
            tid,
            type,
            time: this.parseTime(match[1]),
          });
          this.objectives.push(thread.last);
          break;
        case MarkerType.STARTUP:
        case MarkerType.LABEL:
        case MarkerType.INFO:
          thread.addmarker(id, {
            tid,
            type,
            time: this.parseTime(match[1]),
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
            time: this.parseTime(match[1]),
            backtrail: {
              tid: parseInt(match[2]),
              id: parseInt(match[3])
            }
          });
          break;
        default:
          if (isNaN(type)) {
            break;
          }
          this.assert(false, `Missing new marker handler for ${type}, ${fullLine}`);
      }
    }
  }

  cacheForwardtrail() {
    for (let thread of Object.values(this.threads)) {
      for (let marker of thread.markers) {
        if (!marker.backtrail || !marker.backtrail.id) {
          continue;
        }
        this.get(marker.backtrail).forwardtrail = {
          tid: marker.tid,
          id: marker.id,
        }
      }
    }
  }

  listObjectives() {
    this.objectivesSelector.empty();
    if (!this.objectives.length) {
      this.message("No objective found");
      return;
    }

    if (!this.baseline || this.baseline.objectivesSelector.val() != "0:0:0:0") {
      this.objectivesSelector.prop("disabled", false);
    }

    this.objectivesSelector.append($("<option>").attr("value", `0:0:0:0`).text("Select objective"));
    for (let obj of this.objectives) {
      obj.labels = [];
      obj.source = this.backtrack(obj.tid, obj.id, 0, 0, () => { }, () => { }, (bt, label) => obj.labels.push(label));
      let sources = obj.labels.concat([obj.source]);
      for (let source of sources) {
        let time = obj.time - source.time;
        this.objectivesSelector
          .append($("<option>")
            .attr("value", `${obj.tid}:${obj.id}:${source.tid}:${source.id}`)
            .text(`(${time.toFixed(PREC)}ms) ${obj.names.join("|")} @${obj.time.toFixed(PREC)}ms → ${MarkerType.$(source.type)} ${source.names.join("|")} @${source.time.toFixed(PREC)}ms`)
          );
      }
    }
    this.objectivesSelector.val(`0:0:0:0`);
  }

  baselineProfile(tid, id, btid, bid, indent = 0) {
    breadcrumbs.push(this.get({ tid, id }), { btid, bid }, indent);
    
    let records = [];
    this.backtrack(
      tid, id, btid, bid,
      (bt, marker, className = "") => {
        let last = records.last() || {};
        records.push({ marker, className });
        last.prev = records.last();
      },
      (bt, trail, marker) => { 
        let last = records.last();
        bt.assert(last.marker === marker);

        last.trail = trail;
        last.dependent = marker.rooted;
        last.blockers = [];
        bt.blockers(trail, marker, (bt, blocker) => {
          last.blockers.push(blocker);
        });
      }
    );

    for (let record of records) {
      let { marker, className } = record;
      let prev = record.prev && record.prev.marker;
      let blockers = [];
      let message;
      if (prev) {
        message = `delay: ${(marker.time - prev.time).toFixed(PREC)}ms`;
        if (record.blockers && record.blockers.length) {
          message += `, blocker count: ${record.blockers.length}`;
          blockers = record.blockers.filter(blocker => {
            let edge = Math.min(this.forwardtrail(blocker).time, marker.time);
            let time = edge - blocker.time;
            return time > BLOCKER_LISTING_THRESHOLD_MS;
          });
        }
      }

      if (record.dependent) {
        message += `\n  → dependent execution, click to show the triggering path`;
      }
      let element = display.deferMarker(this, marker, message);
      if (prev) {
        display.deferTimingBar(marker.time - prev.time);
      }
      if (element.level === undefined) {
        element.level = indent;
      }

      if (DEPENDECY_CLICKABLE_IN_SINGLE && record.dependent) {
        element.element.addClass("clickable").on("click", () => {
          let marker = this.prev(record.marker);
          display.reset();
          this.baselineProfile(marker.tid, marker.id, btid, bid, indent /* + 10*/);
          display.flush((elements) => {
            // no need when we reset the display before baseline profile call
            // elements.sort((a, b) => b.marker.time - a.marker.time);
          });
        });
      }

      if (element.level < indent) {
        // We have hit the original path
        element.element.addClass("join");
        break;
      }

      element.element.addClass(className).css({ "margin-left": indent + "%" })

      if (blockers.length) {
        let sub = display.sub($("<div>").addClass("blocker-container"), record.marker);
        sub.defer({ element: $("<span>").text(`click to show blockers`).addClass("clickable").click((e) => {
          for (let blocker of blockers) {
            let forward = this.forwardtrail(blocker);
            let time = forward.time - blocker.time;
            let labels = [];
            let source = this.backtrack(blocker.tid, blocker.id, btid, bid, () => { }, () => { }, (bt, label) => {
              labels.push(label);
            });
            labels.push(source);

            let lastSource;
            let lastLeadName = "";
            let leadNameCounter = 0;
            let sources = labels.reduce((result, source) => {
              let name = source.names.join("|");
              let leadName = name.split(" ")[0];
              if (leadName == lastLeadName) {
                ++leadNameCounter;
                return result;
              }
              if (leadNameCounter) {
                result += `\n  +${leadNameCounter} more ${MarkerType.$(lastSource.type)} "${lastLeadName}" for different resources`;
              }
              lastLeadName = leadName;
              leadNameCounter = 0;
              lastSource = source;
              return result + `\n• ${MarkerType.$(source.type)} "${name}" @${source.time.toFixed(PREC)}ms`;
            }, "");

            sub.deferMarker(this, blocker,
              `self-time: ${time.toFixed(PREC)}ms\nsource events: ${sources}`
            ).element.addClass("blocker alone clickable").click(() => {
              let forward = this.forwardtrail(blocker);
              if (!SHOW_DEPENDENT_PATH_FROM_EXECUTE_END || !forward.id) {
                forward = blocker;
              } else {
                forward = this.prev(forward);
              }
              display.reset();
              this.baselineProfile(forward.tid, forward.id, btid, bid, indent /* + 10*/);
              display.flush();
            });
            sub.deferTimingBar(time);
           } // for blockers
          sub.flush();
          $(e.target).off("click").removeClass("clickable");
        }) });
        sub.flush();
      }
    }
  }

  compareProfiles(tid, id, break_tid, break_id) {
    let collector = function (bt, marker, className) {
      this.push({ marker, desc: bt.descriptor(marker), className });
    };
    let trailCollector = function (bt, trail, marker) {
      bt.assert(this.last().marker === marker);
      this.last().trail = trail;
      this.last().dependent = marker.rooted;
    };

    let [btid, bid, break_btid, break_bid] = this.baseline.objectivesSelector.val().split(":").map(id => parseInt(id));
    let baselinePath = [];
    this.baseline.backtrack(btid, bid, break_btid, break_bid, collector.bind(baselinePath), trailCollector.bind(baselinePath));

    let modifiedPath = [];
    this.backtrack(tid, id, break_tid, break_id, collector.bind(modifiedPath), trailCollector.bind(modifiedPath));

    let total_baseline = baselinePath[0].marker.time - baselinePath.last().marker.time;
    let total_modified = modifiedPath[0].marker.time - modifiedPath.last().marker.time;
    display.defer({ element: $("<pre>").addClass("equal cmp bold").text(
      `OVERALL STATISTICS\nbaseline: ${total_baseline.toFixed(PREC)}ms, modified: ${total_modified.toFixed(PREC)}ms, difference: ${(total_modified - total_baseline).toFixed(PREC)}ms`
    ) });
    display.deferDiffTimingBar(total_baseline, total_modified);
    display.defer({ element: $("<hr>") });

    let compare = LCS(baselinePath, modifiedPath, (a, b) => a.desc === b.desc);

    while (compare.length) {
      let { base, mod } = compare.shift();
      let base_prev = compare.find(e => e.base);
      if (base_prev) {
        base_prev = base_prev.base;
      }
      let mod_prev = compare.find(e => e.mod);
      if (mod_prev) {
        mod_prev = mod_prev.mod;
      }
      let equal_prev = compare.find(e => e.base && e.mod);
      if (equal_prev === compare[0]) {
        // We only want this when there is a diversion ahead
        equal_prev = null;
      }

      if (base && mod) {
        let base_delay = base_prev ? base.marker.time - base_prev.marker.time : 0;
        let mod_delay = mod_prev ? mod.marker.time - mod_prev.marker.time : 0;
        let base_delay_eq = 0;
        let mod_delay_eq = 0;

        display.deferMarker(this.baseline, base.marker,
          `base: +${base_delay.toFixed(PREC)}ms, modified: +${mod_delay.toFixed(PREC)}ms, difference: ${(mod_delay - base_delay).toFixed(PREC)}ms` +
          `${base.dependent ? "\nbaseline is dependent execution" : ""}`+
          `${mod.dependent ? "\nmodified is dependent execution" : ""}`
        ).element.addClass("equal cmp").addClass(base.className);
        display.deferDiffTimingBar(base_delay, mod_delay);

        if (equal_prev) {
          // Calc the times to the next point where path meet each other again.
          base_delay_eq = base.marker.time - equal_prev.base.marker.time;
          mod_delay_eq = mod.marker.time - equal_prev.mod.marker.time;
          display.defer({
            element: $("<pre>").addClass("equal cmp").text(
              `\ndifference to the next equal point: ${(mod_delay_eq - base_delay_eq).toFixed(PREC)}ms`
            )
          });
          display.deferDiffTimingBar(base_delay_eq, mod_delay_eq);
        }

        if (base.trail) {
          this.assert(!!mod.trail, "Equal marker from the modified profile doesn't have a trail");

          let baselineBlockers = [];
          this.baseline.blockers(base.trail, base.marker, collector.bind(baselineBlockers));

          let modifiedBlockers = [];
          this.blockers(mod.trail, mod.marker, collector.bind(modifiedBlockers));

          let blockers = LCS(baselineBlockers, modifiedBlockers, (a, b) => a.desc === b.desc);
          if (SHOW_BLOCKERS_IN_DIFF && blockers.length) {
            let subdisp = display.sub($("<div>").addClass("blocker-container"));
            for (let blocker of blockers) {
              if (blocker.base && blocker.mod) {
                let base = {
                  begin: blocker.base.marker,
                  end: this.baseline.forwardtrail(blocker.base.marker),
                }
                let mod = {
                  begin: blocker.mod.marker,
                  end: this.forwardtrail(blocker.mod.marker),
                }
                let base_time = base.end.time - base.begin.time;
                let mod_time = mod.end.time - mod.begin.time;
                let diff = mod_time - base_time;

                subdisp.deferMarker(this.baseline, blocker.base.marker,
                  `self-time baseline: ${base_time.toFixed(PREC)}ms, modified: ${mod_time.toFixed(PREC)}ms, difference: ${diff.toFixed(PREC)}ms`, true
                ).element.addClass("blocker equal");
                subdisp.deferDiffTimingBar(base_time, mod_time);
              } else if (blocker.base) {
                let base = {
                  begin: blocker.base.marker,
                  end: this.baseline.forwardtrail(blocker.base.marker),
                }
                let base_time = base.end.time - base.begin.time;
                subdisp.deferMarker(this.baseline, blocker.base.marker,
                  `self-time ${base_time.toFixed(PREC)}ms\n`, true
                ).element.addClass("base blocker");
              } else if (blocker.mod) {
                let mod = {
                  begin: blocker.mod.marker,
                  end: this.forwardtrail(blocker.mod.marker),
                }
                let mod_time = mod.end.time - mod.begin.time;
                subdisp.deferMarker(this, blocker.mod.marker,
                  `self-time ${mod_time.toFixed(PREC)}ms\n`, true
                ).element.addClass("mod blocker");
              } else {
                this.assert(false, "No .baseline or .modified on an LCS result (blockers)");
              }
            }
            subdisp.flush();
          }
        }
      } else if (base) {
        let base_delay = base_prev ? base.marker.time - base_prev.marker.time : 0;
        display.deferMarker(this.baseline, base.marker, `base: +${base_delay.toFixed(PREC)}ms`)
          .element.addClass("base cmp").addClass(base.className);
      } else if (mod) {
        let mod_delay = mod_prev ? mod.marker.time - mod_prev.marker.time : 0;
        display.deferMarker(this, mod.marker, `modified: +${mod_delay.toFixed(PREC)}ms`)
          .element.addClass("mod cmp").addClass(mod.className);
      } else {
        this.assert(false, "No .baseline or .modified on an LCS result");
      }
    }
  }

  assert(cond, msg) {
    if (!cond) {
      throw new Error(msg || "Assertion failure");
    }
  }

  assertNot(cond, msg) {
    this.assert(!cond, msg);
  }

  descriptor(marker) {
    let thread = this.threads[marker.tid];
    let process = thread.process;
    let threadName = thread.name.split('#')[0];
    return `${marker.type}@${marker.names.join("|")}@${process.type}@${threadName}`;
  }

  get(gid) {
    if (!gid || !gid.id) {
      return new PlaceholderMarker();
    }
    let index = gid.id - 1; // we count from 1...
    this.assert(index >= 0);
    // Can't enforce the following assertion until we gracefully close BT files on all processes
    /* this.assert(index < this.threads[gid.tid].markers.length); */
    return this.threads[gid.tid].markers[index] || new PlaceholderMarker();
  }

  prev(marker) {
    let index = marker.id - 1; // we count from 1...
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
    let forward_gid = this.get(source).forwardtrail;
    return this.get(forward_gid);
  }

  blockers(dispatch, execute_begin, collector) {
    let pexec_gid = execute_begin.pexec_gid;
    let up_to = this.forwardtrail(execute_begin);

    while (pexec_gid && pexec_gid.id) {
      let execute_begin = this.get(pexec_gid);
      let execute_end = this.forwardtrail(execute_begin);
      if (execute_end.time > dispatch.time && (execute_end.tid !== up_to.tid || execute_end.time < up_to.time)) {
        collector(this, execute_begin);
      }

      pexec_gid = execute_begin.pexec_gid;
    }
  }

  backtrack(tid, id, break_tid, break_id, collector, blocker_trail = () => { }, labels = () => { }) {
    let marker = this.get({ tid, id });
    let label = this.get({ tid: break_tid, id: break_id });
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
        case MarkerType.LOOP_END:
          // Uninteresting, just skip
          marker = this.backtrail(marker);
          marker = this.prev(marker);
          break;
        case MarkerType.REDISPATCH_END:
        case MarkerType.EXECUTE_END:
        case MarkerType.RESPONSE_END:
        case MarkerType.INPUT_END:
          collector(this, marker, "span");
          marker = this.backtrail(marker);
          collector(this, marker, "span");
          marker = this.prev(marker);
          break;
        case MarkerType.LABEL:
          collector(this, marker);
          labels(this, marker);
          if (marker === label) {
            return marker;
          }
          marker = this.prev(marker);
          break;
        default:
          collector(this, marker);
          marker = this.prev(marker);
          break;
      }
    };
  }
}

$(() => {
  $("#objectives1").append($("<option>")
    .attr("value", `0:0:0:0`)
    .text(`Please load files for the baseline profile`)
  ).val(`0:0:0:0`).prop("disabled", true);

  $("#files2").prop("disabled", true);
  $("#objectives2").prop("disabled", true);

  let timeline = $("#timeline").css({ "height": "50%", });
  display = new Display(timeline);

  let baseline = new Backtrack($("#files1"), $("#objectives1"));
  let modified = new Backtrack($("#files2"), $("#objectives2"), baseline);
  baseline.modified = modified;

  breadcrumbs = new Breadcrumb($("#breadcrumbs"), baseline);
});
