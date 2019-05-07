open GrbGraphs;;
open GrbInput;;

let access_granted = [("parameters", "portname"); ("parameters", "deadline"); ("parameters", "param_id"); ("parameters", "portname"); ("parameters", "deadline"); ("parameters", "param_id"); ("ship_2", "ship_id"); ("ship_2", "name"); ("ship_2", "cargo"); ("ship_2", "draft"); ("ship_2", "length"); ("ship_2", "max_speed"); ("ship_2", "latitude"); ("ship_2", "longitude"); ("port_2", "available"); ("port_2", "harbordepth"); ("port_2", "offloadtime"); ("port_2", "offloadcapacity"); ("port_2", "longitude"); ("port_2", "latitude"); ("port_2", "name"); ("port_2", "port_id")];;

let aiddistrDbdesc =
     RLMap.add "port_1"
    (RLMap.add "port_id" VInteger (RLMap.add "port_id" VInteger (RLMap.add "name" VString (RLMap.add "latitude" VInteger (RLMap.add "longitude" VInteger (RLMap.add "offloadcapacity" VInteger (RLMap.add "offloadtime" VInteger (RLMap.add "harbordepth" VInteger (RLMap.singleton "available" VBoolean)))))))), [RLSet.singleton "port_id"])
  (
  RLMap.add "slot"
    (RLMap.add "slot_id" VInteger (RLMap.add "slot_id" VInteger (RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.add "slotstart" VInteger (RLMap.singleton "slotend" VInteger))))), [RLSet.singleton "slot_id"])
  (
  RLMap.add "berth"
    (RLMap.add "berth_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.add "port_id" VInteger (RLMap.singleton "berthlength" VInteger))), [RLSet.singleton "berth_id"])
  (
  RLMap.add "parameters"
    (RLMap.add "ship_id" VInteger (RLMap.add "param_id" VInteger (RLMap.add "deadline" VInteger (RLMap.singleton "portname" VString))), [RLSet.singleton "param_id"])
  (
  RLMap.add "ship_2"
    (RLMap.add "ship_id" VInteger (RLMap.add "ship_id" VInteger (RLMap.add "name" VString (RLMap.add "cargo" VInteger (RLMap.add "latitude" VInteger (RLMap.add "longitude" VInteger (RLMap.add "length" VInteger (RLMap.add "draft" VInteger (RLMap.singleton "max_speed" VInteger)))))))), [RLSet.singleton "ship_id"])
  (
  RLMap.add "port_2"
    (RLMap.add "port_id" VInteger (RLMap.add "port_id" VInteger (RLMap.add "name" VString (RLMap.add "latitude" VInteger (RLMap.add "longitude" VInteger (RLMap.add "offloadcapacity" VInteger (RLMap.add "offloadtime" VInteger (RLMap.add "harbordepth" VInteger (RLMap.singleton "available" VBoolean)))))))), [RLSet.singleton "port_id"])
  (
  RLMap.add "parameters"
    (RLMap.add "param_id" VInteger (RLMap.add "param_id" VInteger (RLMap.add "deadline" VInteger (RLMap.singleton "portname" VString))), [RLSet.singleton "param_id"])
  (
  RLMap.singleton "aggr_count_1"
    (RLMap.add "name" VString (RLMap.add "name" VString (RLMap.singleton "cnt" VInteger)), [RLSet.singleton "name"])
  )))))));;

let aiddistrQuery =
let earliest_arrival ship_lat ship_long port_lat port_long max_speed =
    RAXoper (OPCeiling, [RAXoper (OPDiv, [RAXoper (OPGeoDist, [RAXattribute ship_lat; RAXattribute ship_long; RAXattribute port_lat; RAXattribute port_long]); RAXattribute max_speed])])
in
RALetExp ("port_2",  RARenameCol("p1.port_id", "port_id",
  RARenameCol("p1.name", "name",
  RARenameCol("p1.latitude", "latitude",
  RARenameCol("p1.longitude", "longitude",
  RARenameCol("p1.offloadcapacity", "offloadcapacity",
  RARenameCol("p1.offloadtime", "offloadtime",
  RARenameCol("p1.harbordepth", "harbordepth",
  RARenameCol("p1.available", "available",
    RAProject(
          RARenameCol("port_id", "p1.port_id",
          RARenameCol("name", "p1.name",
          RARenameCol("latitude", "p1.latitude",
          RARenameCol("longitude", "p1.longitude",
          RARenameCol("offloadcapacity", "p1.offloadcapacity",
          RARenameCol("offloadtime", "p1.offloadtime",
          RARenameCol("harbordepth", "p1.harbordepth",
          RARenameCol("available", "p1.available",
            RATable "port_1"
          )))))))),
      ["p1.port_id"; "p1.name"; "p1.latitude"; "p1.longitude"; "p1.offloadcapacity"; "p1.offloadtime"; "p1.harbordepth"; "p1.available"])
  )))))))),
RALetExp ("aggr_count",
  RARenameCol("cnt", "cnt",
    RAProject(
RAAggregate (
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("name", "port_2.name",
          RARenameCol("latitude", "port_2.latitude",
          RARenameCol("longitude", "port_2.longitude",
            RATable "port_2"
          )));
          RARenameCol("portname", "parameters.portname",
          RARenameCol("deadline", "parameters.deadline",
            RATable "parameters"
          ));
          RARenameCol("latitude", "ship_2.latitude",
          RARenameCol("longitude", "ship_2.longitude",
          RARenameCol("max_speed", "ship_2.max_speed",
          RARenameCol("ship_id", "ship_2.ship_id",
            RATable "ship_2"
          ))))
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port_2.name"; RAXattribute "parameters.portname"]); RAXoper (OPLessEqual, [RAXoper (OPDiv, [RAXoper (OPGeoDist, [RAXattribute "ship_2.latitude"; RAXattribute "ship_2.longitude"; RAXattribute "port_2.latitude"; RAXattribute "port_2.longitude"]); RAXattribute "ship_2.max_speed"]); RAXattribute "parameters.deadline"])])
      ),
     "cnt", RAXattribute "ship_2.ship_id"), 
 [], [("cnt", AGCount)]),
      ["cnt"])
  ),
RALetExp ("aggr_count_2",  RARenameCol("p.name", "name",
  RARenameCol("res.cnt", "cnt",
    RAProject(
      RACartesian[
          RARenameCol("name", "p.name",
            RATable "port_2"
          );
          RARenameCol("cnt", "res.cnt",
            RATable "aggr_count"
          )
      ],
      ["p.name"; "res.cnt"])
  )),
RALetExp ("aggr_cargo",
  RARenameCol("sumcargo", "sumcargo",
    RAProject(
RAAggregate (
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("name", "port_2.name",
          RARenameCol("latitude", "port_2.latitude",
          RARenameCol("longitude", "port_2.longitude",
            RATable "port_2"
          )));
          RARenameCol("portname", "parameters.portname",
          RARenameCol("deadline", "parameters.deadline",
            RATable "parameters"
          ));
          RARenameCol("latitude", "ship_2.latitude",
          RARenameCol("longitude", "ship_2.longitude",
          RARenameCol("max_speed", "ship_2.max_speed",
          RARenameCol("cargo", "ship_2.cargo",
            RATable "ship_2"
          ))))
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port_2.name"; RAXattribute "parameters.portname"]); RAXoper (OPLessEqual, [RAXoper (OPDiv, [RAXoper (OPGeoDist, [RAXattribute "ship_2.latitude"; RAXattribute "ship_2.longitude"; RAXattribute "port_2.latitude"; RAXattribute "port_2.longitude"]); RAXattribute "ship_2.max_speed"]); RAXattribute "parameters.deadline"])])
      ),
     "sumcargo", RAXattribute "ship_2.cargo"), 
 [], [("sumcargo", AGSum)]),
      ["sumcargo"])
  ),
RALetExp ("aggr_cargo_2",  RARenameCol("p.name", "name",
  RARenameCol("res.sumcargo", "sumcargo",
    RAProject(
      RACartesian[
          RARenameCol("name", "p.name",
            RATable "port_2"
          );
          RARenameCol("sumcargo", "res.sumcargo",
            RATable "aggr_cargo"
          )
      ],
      ["p.name"; "res.sumcargo"])
  )),
RALetExp ("aggr_count_1",  RARenameCol("ac2.name", "name",
  RARenameCol("ac2.cnt", "cnt",
    RAProject(
          RARenameCol("name", "ac2.name",
          RARenameCol("cnt", "ac2.cnt",
            RATable "aggr_count_2"
          )),
      ["ac2.name"; "ac2.cnt"])
  )),
RALetExp ("slots_count",
  RARenameCol("slots_number", "slots_number",
    RAProject(
RAAggregate (
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("name", "aggr_count_1.name",
            RATable "aggr_count_1"
          );
          RARenameCol("name", "port_1.name",
          RARenameCol("port_id", "port_1.port_id",
          RARenameCol("offloadtime", "port_1.offloadtime",
            RATable "port_1"
          )));
          RARenameCol("portname", "parameters.portname",
          RARenameCol("deadline", "parameters.deadline",
            RATable "parameters"
          ));
          RARenameCol("port_id", "berth.port_id",
          RARenameCol("berth_id", "berth.berth_id",
            RATable "berth"
          ));
          RARenameCol("port_id", "slot.port_id",
          RARenameCol("berth_id", "slot.berth_id",
          RARenameCol("slotstart", "slot.slotstart",
          RARenameCol("slotend", "slot.slotend",
          RARenameCol("slot_id", "slot.slot_id",
            RATable "slot"
          )))))
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "aggr_count_1.name"; RAXattribute "port_1.name"]); RAXoper (OPIsEq, [RAXattribute "port_1.name"; RAXattribute "parameters.portname"]); RAXoper (OPIsEq, [RAXattribute "port_1.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "slot.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "slot.berth_id"; RAXattribute "berth.berth_id"]); RAXoper (OPLessEqual, [RAXattribute "slot.slotstart"; RAXattribute "parameters.deadline"]); RAXoper (OPLessEqual, [RAXoper (OPPlus, [RAXattribute "slot.slotstart"; RAXattribute "port_1.offloadtime"]); RAXattribute "slot.slotend"])])
      ),
     "slots_number", RAXattribute "slot.slot_id"), 
 [], [("slots_number", AGCount)]),
      ["slots_number"])
  ),
RALetExp ("capacities_1",  RARenameCol("p.name", "portname",
  RARenameCol("res.slots_number", "slots_number",
    RAProject(
      RACartesian[
          RARenameCol("name", "p.name",
            RATable "port_1"
          );
          RARenameCol("slots_number", "res.slots_number",
            RATable "slots_count"
          )
      ],
      ["p.name"; "res.slots_number"])
  )),
RALetExp ("capacities_2",  RARenameCol("cap1.portname", "name",
  RARenameCol("cap1.slots_number", "slots_number",
    RAProject(
          RARenameCol("portname", "cap1.portname",
          RARenameCol("slots_number", "cap1.slots_number",
            RATable "capacities_1"
          )),
      ["cap1.portname"; "cap1.slots_number"])
  )),
RALetExp ("ordered_ships",
  RAAddSortColumn (
  RARenameCol("ship_2.ship_id", "ship_id",
  RARenameCol("arrival", "arrival",
  RARenameCol("ship_2.cargo", "cargo",
  RARenameCol("ship_2.draft", "draft",
  RARenameCol("port_2.port_id", "port_id",
    RAProject(
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("longitude", "ship_2.longitude",
          RARenameCol("latitude", "ship_2.latitude",
          RARenameCol("max_speed", "ship_2.max_speed",
          RARenameCol("ship_id", "ship_2.ship_id",
          RARenameCol("cargo", "ship_2.cargo",
          RARenameCol("draft", "ship_2.draft",
            RATable "ship_2"
          ))))));
          RARenameCol("longitude", "port_2.longitude",
          RARenameCol("latitude", "port_2.latitude",
          RARenameCol("port_id", "port_2.port_id",
            RATable "port_2"
          )));
          RARenameCol("deadline", "parameters.deadline",
          RARenameCol("ship_id", "parameters.ship_id",
            RATable "parameters"
          ))
        ],
        RAXoper (OPLessEqual, [earliest_arrival "ship_2.longitude" "ship_2.latitude" "port_2.longitude" "port_2.latitude" "ship_2.max_speed"; RAXattribute "parameters.deadline"])
      ),
     "arrival", earliest_arrival "ship_2.longitude" "ship_2.latitude" "port_2.longitude" "port_2.latitude" "ship_2.max_speed"),
      ["ship_2.ship_id"; "arrival"; "ship_2.cargo"; "ship_2.draft"; "port_2.port_id"])
  ))))),
    "row_id", ["ship_id"], "ship_id"),
RALetExp ("selected_ships",  RARenameCol("os.port_id", "port_id",
  RARenameCol("os.arrival", "arrival",
    RAProject(
      RAFilter (
        RACartesian [
          RARenameCol("row_id", "os.row_id",
          RARenameCol("port_id", "os.port_id",
          RARenameCol("arrival", "os.arrival",
            RATable "ordered_ships"
          )));
          RARenameCol("slots_number", "capacities_2.slots_number",
            RATable "capacities_2"
          )
        ],
        RAXoper (OPLessEqual, [RAXattribute "os.row_id"; RAXattribute "capacities_2.slots_number"])
      ),
      ["os.port_id"; "os.arrival"])
  )),
  RATable "selected_ships"
)))))))))));;
