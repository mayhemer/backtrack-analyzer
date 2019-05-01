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
  LABEL_BEGIN: 17,
  LABEL_END: 18,
  LOOP_BEGIN: 19,
  LOOP_END: 20,
  STARTUP: 21,
  INFO: 22,
  MILESTONE: 23,

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
const BLOCKER_IN_DIFF_TH = 80;
const SHOW_BLOCKERS_IN_SINGLE = false;
const BLOCKER_LISTING_THRESHOLD_MS = 0;
const DEPENDECY_CLICKABLE_IN_SINGLE = true;
const SHOW_BLOCKER_PATH_FROM_EXECUTE_END = true;
const COALESCE_LABELS_IN_BLOCKER_LIST = false;
const COALESCE_INFO_MARKERS = false;
const SHOW_INTERMEDIATE_LABELS_FOR_OBJECTIVES = false;
const PATH_DOWNLOAD_LIMIT_DEPENDENT_EXECS = 40;
const LAZY_PATH_LOAD_BATCH = 500;

let SHOW_ONLY_MILESTONES = false;
let OMIT_NESTED_BLOCKS = false;

const voidOnLoadMore = (_) => { };
var onLoadMore = voidOnLoadMore;

const FILE_SLICE = 256 << 10;
const PREC = 2;

function exposeDownload(data, fileName, filter) {
  let json = JSON.stringify(data, filter, " ");
  let blob = new Blob([json], { type: "octet/stream" });
  let url = window.URL.createObjectURL(blob);

  $("#download-path").show();
  let a = document.getElementById("download-path");
  if (a.href) {
    window.URL.revokeObjectURL(a.href);
  }
  a.href = url;
  a.download = fileName;
}

function _may_fail(f) {
  try {
    f();
  } catch (ex) {
  }
}

function ensure(array, itemName, def = {}) {
  if (!(itemName in array)) {
    array[itemName] = (typeof def === "function") ? def() : def;
  }

  return array[itemName];
}

function consumeGenerator(generator, filter = i => i) {
  let item = generator.next();
  let results = [];
  while (!item.done) {
    let filtered = filter(item.value);
    if (filtered) {
      results.push(filtered);
    }

    item = generator.next();

    if (filtered === false) {
      break;
    }
  }
  return results;
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
    for (let { marker, revert, scroll, footRecord } of this.history) {
      this.target.append(" &gt; ");
      this.target.append($("<span>").text(
        `${MarkerType.$(marker.type)} "${marker.names.reduce((result, name) => {
          if (result.length > 25) {
            return result;
          }
          if (result) result += " ";
          return result += name;
        }, "")}"`
      ).click(() => {
        let drop = false;
        this.history = this.history.filter((bc) => {
          return !(drop || (drop = bc.marker === marker));
        });
        revert(footRecord);
        display.flush();
        $(window).scrollTop(scroll);
      }));
    }
  }

  push(marker, revert) {
    if (this.history.length) {
      this.history.last().scroll = $(window).scrollTop();
      this.history.last().footRecord = this.bt.footRecord;
    }
    this.history.push({
      marker,
      revert,
      scroll: 0,
      footRecord: null,
    });
    this.rebuild();
  }
}

class Display {
  constructor(timeline, master = true) {
    this.timeline = timeline;
    this.reset(master);
  }

  reset(master = true) {
    this.defered = [];
    this.known = [];
    this.markers = {};
    this.timeline.empty();
    this.nextNonInfo = 1;

    if (master) {
      $(window).scrollTop(0);
    }
  }

  gid(marker) {
    return `${marker.tid}:${marker.id}`; // assume tids are unique cross profiles...
  }

  sub(target, marker) {
    this.defer({ element: target, marker });
    return new Display(target, false);
  }

  defer(element) {
    element.order = this.known.length;
    this.defered.push(element);
    this.known.push(element);
    return element;
  }

  deferMarker(bt, marker, msg = "", short = false) {
    let mod = null;
    if (Array.prototype.isPrototypeOf(marker)) {
      mod = marker[1];
      marker = marker[0];
    }

    let names = marker.names;
    if (!names.length) {
      // No name on EXECUTE?  Fall back to DISPATCH
      switch (marker.type) {
        case MarkerType.EXECUTE_BEGIN:
        case MarkerType.RESPONSE_BEGIN:
          _may_fail(() => names = bt.get(marker.backtrail).names);
      }
    }

    if (mod) {
      let informationalNamesMod = mod.names.filter(name => name.match(/^\?\:/));
      names = names.concat(informationalNamesMod);
    }

    let element = this.markers[this.gid(marker)];
    if (!element) {
      let thread = bt.threads[marker.tid];
      let process = thread.process;
      let text = `${MarkerType.$(marker.type)} "${names.join("|")}" @${marker.time.toFixed(PREC)}ms`;
      if (marker.type !== MarkerType.INFO) {
        text +=
          (mod ? `|${mod.time.toFixed(PREC)}ms` : "") +
          (short ? "" : `\n  ${process.name}/${thread.name}  `) +
          (msg ? `\n${msg}` : "");
      }
      element = $("<pre>").text(text).addClass(`marker-type-${MarkerType.$(marker.type).toLowerCase()}`);
      if (marker.type == MarkerType.INFO) {
        let nextNonInfo = this.nextNonInfo;
        element.addClass("clickable").click(() => {
          location.hash = `ref-${nextNonInfo}`;
        });
      } else {
        element.prop("id", `ref-${this.nextNonInfo++}`);
      }

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
      .addClass(diff < 0 ? "plus" : diff > 0 ? "minus" : "")
      .css("width", `${Math.min(100, Math.max(0, Math.abs(diff))) / 2}%`)
      .prop("title", `The modified profile is ${diff > 0 ? "slower" : "faster"}`)
    );
    return this.defer({ element });
  }

  deferTimingBar(time) {
    let factor = Math.floor(time) / 10 * 5;
    let element = $("<div>").addClass("full-width");
    let width = Math.min(100, Math.max(0, Math.abs(factor)));
    if (width < 1) {
      return null;
    }
    element.append($("<div>")
      .addClass("diff-progress single")
      .css("width", `${width}%`)
      .prop("title", `Delay: ${time.toFixed(PREC)}ms`)
    );
    return this.defer({ element });
  }

  flush(sort = () => { }) {
    let elements = Object.values(this.defered);
    this.defered = [];
    sort(elements);

    for (let element of elements) {
      this.timeline.append(element.element);
    }
  }
};

let display, breadcrumbs, operation;

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
        if (params.stop) {
          return null;
        }
        if ($.trim(params.term).length < 3) {
          params.stop = true;
          return { text: "Type at least 3 chars" };
        }
        if (typeof data.text === 'undefined') {
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

    let objectiveHandler = () => {
      window.onLoadMore = voidOnLoadMore;
      display.reset();
      breadcrumbs.reset();
      location.hash = "";
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
    };

    // There is always only one!
    let searchField = () => $("input.select2-search__field");
    this.objectivesSelector.on("change", () => {
      operation = objectiveHandler;
      operation();
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

    setTimeout(() => files.trigger("change"), 0);
  }

  isMilestone(marker) {
    if (!SHOW_ONLY_MILESTONES) {
      return true;
    }
    switch (marker.type) {
      case MarkerType.OBJECTIVE:
      case MarkerType.MILESTONE:
      case MarkerType.INPUT_BEGIN:
      case MarkerType.LABEL_BEGIN:
        return true;
      default:
        return false;
    }
  }

  sources(marker) {
    let labels = [];
    if (marker.type == MarkerType.LABEL_BEGIN) {
      // We want labels to have themselves as a source label, but can't do this inside
      // backtrack() as we would not be able to find the previous label in the loop below.
      labels.push(marker);
    }
    let label = marker.label;
    while (label && label.marker) {
      labels.push(label.marker);
      label = label.marker.label;
    }
    return labels;
  }

  sourcesDescriptor(marker, det = ">", limit) {
    return this.sources(marker).slice(0, limit).map(source => source.names.join("|")).join(det);
  }

  message(msg) {
    this.objectivesSelector.empty().append($("<option>")
      .attr("value", `0:0:0:0`).text(msg)
    ).val("0:0:0:0");
  }

  consumeURL(URI) {
    this.message(`Fetching...`);

    let contentType = '';
    fetch(URI, { mode: 'cors', credentials: 'omit', }).then(function (response) {
      if (response.headers.has('content-type')) {
        contentType = response.headers.get('content-type');
      }
      return response.blob();
    }).then(function (blob) {
      if (contentType.match("zip")) {
        this.consumeZIP(blob);
      } else {
        this.pathProfileFromBlob(blob);
      }
    }.bind(this)).catch((reason) => {
      this.message(reason);
    });
  }

  consumeZIP(blob) {
    this.message(`Unzipping...`);
    zip.createReader(new zip.BlobReader(blob),
      (reader) => {
        reader.getEntries((entries) => {
          let data = [];
          let count = 0;
          for (let entry of entries) {
            data.push(new Promise((resolve) => {
              entry.getData(
                new zip.BlobWriter(),
                (blob) => {
                  blob.name = entry.filename;
                  this.message(`Unzipped ${++count} of ${entries.length}`);
                  resolve(blob);
                },
                (prog) => { }
              );
            }));
          }
          Promise.all(data).then((data) => {
            this.files = data;
            this.consumeFiles();
          });
        });
      },
      (error) => {
        console.error(error);
      }
    );
  }

  consumeFiles() {
    performance.mark("consume-all-begin");

    operation = null;
    window.onLoadMore = voidOnLoadMore;
    display.reset();
    if (breadcrumbs) {
      breadcrumbs.reset();
    }

    this.objectives = [];
    this.processes = {};
    this.threads = {};
    this.startupmarkers = [];

    if (this.files.length == 0) {
      return;
    }

    this.message(`Loading...`);

    if (this.files[0].name.match(/\.btpath$/)) {
      this.pathProfileFromBlob(this.files[0]);
      return;
    }

    if (this.files[0].name.match(/\.zip$/)) {
      this.consumeZIP(this.files[0]);
      return;
    }

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
            lines: [previousLine],
            last: true,
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
            if (!file.last) {
              this.message(`Error during file read: ${ex.message || ex}`);
              throw ex;
            }
          }
        }
      }
    }

    this.info = { CPUS: 1 };
    for (let startup of this.startupmarkers) {
      let info = startup.names.join(" ");
      this.info.CPUS = (cpus => cpus ? cpus[1] : 1)(info.match(/CPUS=(\d+)/));

      // Whipe the name so it doesn't cause any confusions.
      startup.names = [];
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
    return parseFloat(timeString.replace(",", ".")) * 1000;
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
              bt.assert(this.rooting.pop() === true, "rooting not true");
              break;
            case MarkerType.LOOP_END:
              bt.assert(this.rooting.pop() === false, "rooting not false");
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
      thread.name = `${match[0]}(${tid & 0xffff})`;
      if (!thread.time) {
        thread.time = match[1];
      }
    } else if (id === "NP") {
      process.name = `${match[0]}(${process.pid})`.replace('_', ':');
      process.type = match[0];
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
              this.last_name_amend.names.push(`[on queue: ${match.slice(2).join(":")}]`);
              break;
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
          thread.addmarker(id, {
            tid,
            type,
            time: this.parseTime(match[1]),
          });
          this.startupmarkers.push(thread.last);
          break;
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
        case MarkerType.LABEL_BEGIN:
        case MarkerType.ROOT_END:
        case MarkerType.INPUT_END:
        case MarkerType.REDISPATCH_END:
        case MarkerType.EXECUTE_END:
        case MarkerType.RESPONSE_END:
        case MarkerType.LOOP_END:
        case MarkerType.LABEL_END:
        case MarkerType.SLEEP:
        case MarkerType.WAKE:
        case MarkerType.MILESTONE:
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
      try {
        obj.labels = consumeGenerator(this.backtrack(obj.tid, obj.id, 0, 0), item => {
          if (SHOW_INTERMEDIATE_LABELS_FOR_OBJECTIVES) {
            return item.label || item.source;
          }
          return item.source;
        });
      } catch (ex) {
        obj.labels = [];
      }
      obj.source = obj.labels.length && obj.labels.last();
      for (let source of obj.labels) {
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

  setPicker(callback) {
    this.picker = callback;
  }

  pathProfileFromBlob(blob) {
    breadcrumbs.reset();

    let reader = new FileReader();
    reader.onloadend = (event) => {
      if (event.target.readyState == FileReader.DONE && event.target.result) {
        let pathJSON = event.target.result;
        this.pathProfileFromJSONString(pathJSON);
      }
    };
    reader.onerror = () => {
      console.error(`Error while reading stored path`);
      console.exception(reader.error);
      this.message(reader.error);
    };
    reader.readAsBinaryString(blob);
  }

  pathProfileFromJSONString(json) {
    let path = JSON.parse(json);
    let { objective, threads, btid, bid } = path;

    this.threads = threads;

    // tid and id properties are deliberately removed from saved path
    // as we can easily reconstruct them
    for (let threadid in this.threads) {
      let thread = this.threads[threadid];
      thread.tid = threadid;
      for (let index in thread.markers) {
        let marker = thread.markers[index];
        marker.tid = thread.tid;
        marker.id = parseInt(index) + 1;
      }
    }

    display.reset();
    this.baselineProfile(objective.tid, objective.id, btid, bid, false);
    display.flush();
    this.message(objective.names.join("|"));
  }

  collectBacktrackRecords(tid, id, btid, bid, options = {
    limit: 1000000,
    stoponhit: false,
  }) {
    // *_BEGIN may be hit as nested, so there can be a different way of walking
    // them.  Rather ignore hit to not break the different path follow.
    let ignroreHit = new Set([
      MarkerType.ROOT_BEGIN,
      MarkerType.REDISPATCH_BEGIN,
      MarkerType.RESPONSE_BEGIN,
      MarkerType.EXECUTE_BEGIN,
      MarkerType.INPUT_BEGIN,
    ]);

    let count = 0;
    let generator = this.backtrack(tid, id, btid, bid);
    return consumeGenerator(generator, (record) => {
      let { marker } = record;

      if (record.trail) {
        this.blockers(record.trail, marker, (bt, blocker) => {
          bt.forwardtrail(blocker);
        });
      }

      let overlimit = ++count >= options.limit;
      let baselineHit = options.stoponhit && marker.hit_base && !ignroreHit.has(marker.type);

      return !overlimit && !baselineHit ? undefined : false;
    });
  }

  baselineProfile(tid, id, btid, bid, fullProfile = true, footRecord = null) {
    let records = [];
    let threads = {};
    for (let threadid in this.threads) {
      let { process, tid, name } = this.threads[threadid];
      threads[threadid] = {
        process,
        tid,
        name,
        markers: {},
      };
    }

    const COLORING_BASE = 1;
    const COLORING_DEP = 2;
    let coloring = COLORING_BASE;

    if (fullProfile) {
      this.setPicker((threadid, index, marker) => {
        threads[threadid].markers[index] = marker;
        if (coloring == COLORING_BASE) {
          marker.hit_base = true;
        }
      });

      $("#prepare-path").show().click(() => {
        $("#prepare-path").hide();
        coloring = COLORING_DEP;
        let depCount = PATH_DOWNLOAD_LIMIT_DEPENDENT_EXECS;
        for (let record of records) {
          if (record.dependent) {
            if (!depCount) {
              break;
            }
            --depCount;

            // This will color the markers only
            let marker = this.prev(record.marker);
            let { tid, id } = marker;
            this.collectBacktrackRecords(tid, id, btid, bid, {
              limit: 1000,
              stoponhit: true,
            });
          }
        }

        this.setPicker();

        for (let tid of Object.keys(threads)) {
          if (!Object.values(threads[tid].markers).length) {
            delete threads[tid];
          }
        }
        for (let thread of Object.values(threads)) {
          for (let marker of Object.values(thread.markers)) {
            marker.hit_base = undefined;
          }
        }

        let objective = this.get({ tid, id });
        let filename = objective.names.join("_");
        exposeDownload(
          {
            threads,
            objective,
            btid,
            bid
          },
          `${filename}@${objective.time.toFixed(PREC)}.btpath`,
          function (key, val) {
            // "label" reconstructs via backtrack()
            // "tid" and "id" can be easily reconstructed from tables' keys
            // but only for the markers
            if (((this.type && this.type != MarkerType.OBJECTIVE && this.time) || (this.markers)) &&
              (key == "label" || key === "id" || key === "tid")) {
              return undefined;
            }
            return val;
          }
        );
      });
    } else {
      $("#prepare-path").hide();
    }

    let objective = this.get({ tid, id });
    breadcrumbs.push(objective, (footRecord) => {
      this.baselineProfile(tid, id, btid, bid, fullProfile, footRecord);
    });

    display.reset();
    $("#download-path").hide();
    this.footRecord = { marker: null };

    let generator = this.backtrack(tid, id, btid, bid);
    let firstInfo = null;
    let current = generator.next();
    if (current.done) {
      return;
    }

    current = current.value;
    let loadRecord = () => {
      if (!current) {
        return true;
      }

      let preceeding = null;
      do {
        const next = generator.next();
        if (next.done) {
          break;
        }

        preceeding = next.value;
      } while (!this.isMilestone(preceeding.marker));

      let record = current;
      record.prev = preceeding;

      records.push(record);
      let { marker } = record;

      if (record.trail) {
        record.dependent = marker.rooted;
        record.blockers = [];
        this.blockers(record.trail, marker, (bt, blocker) => {
          record.blockers.push(blocker);
          let forward = bt.forwardtrail(blocker);
          blocker.duration = forward.time - blocker.time;
        });
      }

      let isInfo = marker.type == MarkerType.INFO;
      if (COALESCE_INFO_MARKERS) {
        if (isInfo && marker.names.join("|") === (firstInfo && firstInfo.names.join("|"))) {
          return;
        }

        if (firstInfo) {
          let element = $("<div>").addClass("full-width marker-type-info")
            .text(`... multiple times, additional delay: ${(firstInfo.time - marker.time).toFixed(PREC)}ms`);
          display.defer({ element });
          display.deferTimingBar(firstInfo.time - marker.time);
        }
        firstInfo = isInfo ? marker : null;
      }

      let prevMarker = record.prev && record.prev.marker;

      let blockers = [];
      let message;
      if (prevMarker) {
        message = `delay: ${(marker.time - prevMarker.time).toFixed(PREC)}ms`;
        if (record.blockers && record.blockers.length) {
          message += `, blocker count: ${record.blockers.length}`;
          blockers = record.blockers.filter(blocker => {
            if (!fullProfile || !BLOCKER_LISTING_THRESHOLD_MS) {
              return true;
            }
            let time = Math.min(marker.time - blocker.timer, blocker.duration);
            return time > BLOCKER_LISTING_THRESHOLD_MS;
          });
        }
      }

      if (record.dependent) {
        message += `\n  → dependent execution, click to show the triggering path`;
      }

      let defered = display.deferMarker(this, marker, message);
      defered.element.addClass(record.className);
      if (prevMarker) {
        display.deferTimingBar(marker.time - prevMarker.time);
      }

      defered.element.hover(() => {
        let sources = this.sourcesDescriptor(marker, "→\n");
        if (sources) {
          defered.element.prop("title", `source:\n ${sources}`);
        }
        defered.element.off("hover");
      });

      if (DEPENDECY_CLICKABLE_IN_SINGLE && record.dependent) {
        defered.element.addClass("clickable").on("click", () => {
          let marker = this.prev(record.marker);
          try {
            this.baselineProfile(marker.tid, marker.id, btid, bid, fullProfile);
          } catch (ex) { }
          display.flush();
        });
      }

      if (record.className == "span" && record.marker.type == MarkerType.EXECUTE_END) {
        // This is the nested block
        defered.element.addClass("clickable").on("click", () => {
          let marker = this.prev(record.marker);
          this.baselineProfile(marker.tid, marker.id, btid, bid, fullProfile);
          display.flush();
        });
      }

      if (blockers.length) {
        let sub = display.sub($("<div>").addClass("blocker-container"), record.marker);
        sub.defer({ element: $("<span>").text(`click to show blockers`).addClass("clickable gray").click((e) => {
          for (let blocker of blockers) {
            // Can't use this.sources() here since we need to backtrack from this point first to cache labels
            let labels = [];
            if (fullProfile) {
              labels = consumeGenerator(this.backtrack(blocker.tid, blocker.id, btid, bid), item => (item.label || item.source));
            }

            let lastSource;
            let lastLeadName = "";
            let leadNameCounter = 0;
            let sources = labels.reduce((result, source) => {
              let name = source.names.join("|");
              let leadName = name.split(" ")[0];
              if (COALESCE_LABELS_IN_BLOCKER_LIST && leadName == lastLeadName) {
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

            let { element } = sub.deferMarker(this, blocker,
              `self-time: ${blocker.duration.toFixed(PREC)}ms\nsource events: ${sources}`
            );
            element.addClass("blocker alone");
            if (fullProfile) {
              element.addClass("clickable").click(() => {
                let forward = this.forwardtrail(blocker);
                if (!SHOW_BLOCKER_PATH_FROM_EXECUTE_END || !forward.id) {
                  forward = blocker;
                } else {
                  forward = this.prev(forward);
                }
                this.baselineProfile(forward.tid, forward.id, btid, bid, true);
                display.flush();
              });
            }
            sub.deferTimingBar(blocker.duration);
           } // for blockers
          sub.flush();
          $(e.target).off("click").removeClass("clickable");
        }) });
        sub.flush();
      }

      this.footRecord = current;

      current = preceeding;
      if (!current) {
        window.onLoadMore = voidOnLoadMore;
      }
    } // loadRecord()

    let loadBatch = () => {
      for (let load = 0; load < LAZY_PATH_LOAD_BATCH; ++load) {
        loadRecord();
      }
      display.flush();
    }

    window.onLoadMore = (atBottom) => {
      if (atBottom) {
        loadBatch();
      }
    }

    if (footRecord) {
      while (this.footRecord.marker !== footRecord.marker && !loadRecord()) {
      }
      display.flush();
      return;
    } 

    loadBatch();
  }

  compareProfiles(tid, id, break_tid, break_id) {
    // WARNING:
    // This code has been migrated to bactrack() as a generator, but has not been tested since then,
    // as it's not currently used as a critical feature.
    
    let [btid, bid, break_btid, break_bid] =
      this.baseline.objectivesSelector.val().split(":").map(id => parseInt(id));

    const filter = function(record) {
      if (!this.isMilestone(record.marker)) {
        return undefined;
      }
      record.dependent = record.trail && record.marker.rooted;
      return record;
    }
    let baselinePath = consumeGenerator(
      this.baseline.backtrack(btid, bid, break_btid, break_bid), filter.bind(this.baseline)
    );
    let modifiedPath = consumeGenerator(
      this.backtrack(tid, id, break_tid, break_id), filter.bind(this)
    );

    // must be done after calling backtrack(), because only now all labels are correctly set on markers
    for (let marker of baselinePath) {
      marker.desc = this.baseline.descriptor(marker.marker);
    }
    for (let marker of modifiedPath) {
      marker.desc = this.descriptor(marker.marker);
    }

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
        let sourcesL = this.sourcesDescriptor(base.marker, "→\n");
        let sourcesR = this.sourcesDescriptor(mod.marker, "→\n");

        display.deferMarker(this.baseline, [base.marker, mod.marker],
          `base: +${base_delay.toFixed(PREC)}ms, modified: +${mod_delay.toFixed(PREC)}ms, difference: ${(mod_delay - base_delay).toFixed(PREC)}ms` +
          `${base.dependent ? "\nbaseline is dependent execution" : ""}`+
          `${mod.dependent ? "\nmodified is dependent execution" : ""}`
        ).element.addClass("equal cmp").addClass(base.className).prop("title", `source baseline:\n ${sourcesL}\n\nsources mod:\n${sourcesR}`);

        if (equal_prev) {
          // Calc the times to the next point where paths meet each other again.
          base_delay_eq = base.marker.time - equal_prev.base.marker.time;
          mod_delay_eq = mod.marker.time - equal_prev.mod.marker.time;
          display.defer({
            element: $("<pre>").addClass("equal cmp").text(
              `\nto the next equal point, base: ${base_delay_eq.toFixed(PREC)}ms, modified: ${mod_delay_eq.toFixed(PREC)}ms, difference: ${(mod_delay_eq - base_delay_eq).toFixed(PREC)}ms`
            )
          });
          display.deferDiffTimingBar(base_delay_eq, mod_delay_eq);
        } else {
          display.deferDiffTimingBar(base_delay, mod_delay);
        }

        if (base.trail) {
          this.assert(!!mod.trail, "Equal marker from the modified profile doesn't have a trail");

          const collector = function (bt, marker, className) {
            if (!bt.isMilestone(marker)) {
              return true;
            }
            this.push({ marker, className });
            return true;
          };

          let baselineBlockers = [];
          this.baseline.blockers(base.trail, base.marker, collector.bind(baselineBlockers));
          let modifiedBlockers = [];
          this.blockers(mod.trail, mod.marker, collector.bind(modifiedBlockers));

          let delay_diff = Math.abs(base_delay - mod_delay);

          let blockers = LCS(baselineBlockers, modifiedBlockers, (a, b) => a.desc === b.desc);
          if (blockers.length) {
            let sub = display.sub($("<div>").addClass("blocker-container"), base.marker);
            sub.defer({
              element: $("<span>").text(`click to show blockers`).addClass("clickable").click((e) => {
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

                    sub.deferMarker(this.baseline, [blocker.base.marker, blocker.mod.marker],
                      `self-time baseline: ${base_time.toFixed(PREC)}ms, modified: ${mod_time.toFixed(PREC)}ms, difference: ${diff.toFixed(PREC)}ms`, true
                    ).element.addClass("blocker equal");
                    sub.deferDiffTimingBar(base_time, mod_time);
                  } else if (blocker.base) {
                    let base = {
                      begin: blocker.base.marker,
                      end: this.baseline.forwardtrail(blocker.base.marker),
                    }
                    let base_time = base.end.time - base.begin.time;
                    sub.deferMarker(this.baseline, blocker.base.marker,
                      `self-time ${base_time.toFixed(PREC)}ms\n`, true
                    ).element.addClass("base blocker");
                  } else if (blocker.mod) {
                    let mod = {
                      begin: blocker.mod.marker,
                      end: this.forwardtrail(blocker.mod.marker),
                    }
                    let mod_time = mod.end.time - mod.begin.time;
                    sub.deferMarker(this, blocker.mod.marker,
                      `self-time ${mod_time.toFixed(PREC)}ms\n`, true
                    ).element.addClass("mod blocker");
                  } else {
                    this.assert(false, "No .baseline or .modified on an LCS result (blockers)");
                  }
                }
                sub.flush();
                $(e.target).off("click").removeClass("clickable");
              })
            });
            sub.flush();
          }
        }
      } else if (base) {
        let base_delay = base_prev ? base.marker.time - base_prev.marker.time : 0;
        let sources = this.sourcesDescriptor(base.marker, "→\n");
        display.deferMarker(this.baseline, base.marker, `base: +${base_delay.toFixed(PREC)}ms`)
          .element.addClass("base cmp").addClass(base.className).prop("title", `source:\n ${sources}`);
      } else if (mod) {
        let mod_delay = mod_prev ? mod.marker.time - mod_prev.marker.time : 0;
        let sources = this.sourcesDescriptor(mod.marker, "→\n");
        display.deferMarker(this, mod.marker, `modified: +${mod_delay.toFixed(PREC)}ms`)
          .element.addClass("mod cmp").addClass(mod.className).prop("title", `source:\n ${sources}`);
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
    let sources = this.sourcesDescriptor(marker, ">", 1);
    return `${marker.type}@${marker.names.filter(name => !name.match(/^\?\:/)).join("|")}@${process.type}@${threadName}@@${sources}`;
  }

  get(gid) {
    if (!gid || !gid.id) {
      return new PlaceholderMarker();
    }
    let index = gid.id - 1; // we count from 1...
    this.assert(index >= 0, "get() with id < 0");
    // Can't enforce the following assertion until we gracefully close BT files on all processes
    /* this.assert(index < this.threads[gid.tid].markers.length); */
    let result = this.threads[gid.tid].markers[index] || new PlaceholderMarker();
    if (this.picker) {
      this.picker(gid.tid, index, result);
    }
    return result;
  }

  prev(marker) {
    return this.get({ tid: marker.tid, id: marker.id - 1 });
  }

  backtrail(marker) {
    this.assert(marker.backtrail, "Expected backtrail");
    this.assert(marker.backtrail.id, "Expected valid backtrail");
    let trail = this.get(marker.backtrail);
    switch (marker.type) {
      case MarkerType.REDISPATCH_END:
      case MarkerType.EXECUTE_END:
      case MarkerType.RESPONSE_END:
      case MarkerType.ROOT_END:
      case MarkerType.INPUT_END:
      case MarkerType.LOOP_END:
      case MarkerType.LABEL_END:
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

      this.assert(pexec_gid.id !== execute_begin.pexec_gid.id || pexec_gid.tid !== execute_begin.pexec_gid.tid,
        `prev-exec loop to itself: gid_t = ${pexec_gid.tid}:${pexec_gid.id}`);
      pexec_gid = execute_begin.pexec_gid;
    }
  }

  *backtrack(tid, id, break_tid, break_id) {
    let marker = this.get({ tid, id });
    const stop = this.get({ tid: break_tid, id: break_id });

    let lazyLabel = { marker: null };
    const result = (marker, props = {}) => {
      if (props.label || props.source) {
        lazyLabel.marker = marker;
        lazyLabel = { marker: null };
      } else {
        marker.label = lazyLabel;
      }

      return Object.assign({
        marker,
        className: '',
      }, props);
    }

    while (marker) {
      switch (marker.type) {
        case MarkerType.ROOT_BEGIN:
          if (marker.rooted) {
            // Uninteresting
            // yield result(marker, { className: "span" });
            marker = this.prev(marker);
            break;
          } // else fall through
        case MarkerType.INPUT_BEGIN:
        case MarkerType.STARTUP:
          yield result(marker, { source: marker });
          return;
        case MarkerType.DISPATCH:
        case MarkerType.REQUEST:
          marker = this.prev(marker);
          break;
        case MarkerType.REDISPATCH_BEGIN:
        case MarkerType.EXECUTE_BEGIN:
        case MarkerType.RESPONSE_BEGIN:
          let trail = this.backtrail(marker);
          yield result(marker, { trail });
          yield result(trail);
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
        case MarkerType.LABEL_END:
        case MarkerType.INPUT_END:
          if (!OMIT_NESTED_BLOCKS) yield result(marker, { className: "span" });
          marker = this.backtrail(marker);
          if (!OMIT_NESTED_BLOCKS) yield result(marker, { className: "span" });
          marker = this.prev(marker);
          break;
        case MarkerType.LABEL_BEGIN:
          yield result(marker, { label: marker });
          if (marker === stop) {
            return;
          }
          marker = this.prev(marker);
          break;
        default:
          yield result(marker);
          marker = this.prev(marker);
          break;
      }
    };
  }
}

$(() => {
  zip.workerScripts = {
    inflater: ['zip/z-worker.js', 'zip/inflate.js']
  };

  $("#objectives1").append($("<option>")
    .attr("value", `0:0:0:0`)
    .text(`Please load files for the baseline profile`)
  ).val(`0:0:0:0`).prop("disabled", true);

  $("#files2").prop("disabled", true);
  $("#objectives2").prop("disabled", true);

  $("#only-milestones").on("change", (event) => {
    SHOW_ONLY_MILESTONES = $(event.target).is(":checked");
    operation && operation();
  }).trigger("change");

  $("#omit-nested").on("change", (event) => {
    OMIT_NESTED_BLOCKS = $(event.target).is(":checked");
    operation && operation();
  }).trigger("change");

  $("#download-path").hide();

  ((selector) => {
    const options = {
      root: null,
    };

    const observer = new IntersectionObserver((entries) => {
      const entry = entries[0];
      window.onLoadMore(entry.isIntersecting);
    }, options);

    let target = document.querySelector(selector);
    observer.observe(target);
  })("#footer");

  let timeline = $("#timeline");
  display = new Display(timeline);

  let baseline = new Backtrack($("#files1"), $("#objectives1"));
  let modified = new Backtrack($("#files2"), $("#objectives2"), baseline);
  baseline.modified = modified;

  breadcrumbs = new Breadcrumb($("#breadcrumbs"), baseline);

  let URL = location.search.substring(1);
  if (URL) {
    baseline.consumeURL(URL);
  }
});
