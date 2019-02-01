open GrbGraphs;;
open GrbInput;;

let access_granted = [("parameters", "shipname"); ("parameters", "deadline"); ("ship", "name"); ("port", "port_id"); ("port", "latitude"); ("port", "longitude"); ("berth", "berth_id"); ("port", "offloadcapacity"); ("port", "harbordepth"); ("port", "available"); ("berth", "berthlength"); ("slot", "slot_id"); ("berth", "port_id"); ("slot", "berth_id"); ("slot", "port_id"); ("ship", "ship_id")];;

let orig_aiddistrDbdesc =
     RLMap.add "slot"
    (RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.add "slot_id" VInteger (RLMap.add "ship_id" VInteger (RLMap.add "slotstart" VInteger (RLMap.singleton "slotend" VInteger))))), [RLSet.from_list ["port_id"; "berth_id"; "slot_id"]])
  (
  RLMap.add "berth"
    (RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.singleton "berthlength" VInteger)), [RLSet.from_list ["port_id"; "berth_id"]])
  (
  RLMap.add "port"
    (RLMap.add "port_id" VInteger (RLMap.add "name" VString (RLMap.add "latitude" VReal (RLMap.add "longitude" VReal (RLMap.add "offloadcapacity" VInteger (RLMap.add "offloadtime" VInteger (RLMap.add "harbordepth" VInteger (RLMap.singleton "available" VBoolean))))))), [RLSet.singleton "port_id"])
  (
  RLMap.add "ship"
    (RLMap.add "ship_id" VInteger (RLMap.add "name" VString (RLMap.add "cargo" VInteger (RLMap.add "latitude" VReal (RLMap.add "longitude" VReal (RLMap.add "length" VInteger (RLMap.add "draft" VInteger (RLMap.singleton "maxspeed" VInteger))))))), [RLSet.singleton "ship_id"])
  (
  RLMap.singleton "parameters"
    (RLMap.add "param_id" VUnit (RLMap.add "deadline" VInteger (RLMap.singleton "shipname" VString)), [RLSet.singleton "param_id"])
  ))));;

let simpleCountDbdesc =
	RLMap.singleton "t1" (RLMap.add "y" VInteger (RLMap.add "x" VInteger (RLMap.singleton "t1_id" VInteger)), [RLSet.singleton "t1_id"]);;

let simpleCountQuery =
	RAProject (RAAggregate (RATable "t1", ["y"], [("x", AGCount)]), ["x"]);;

(* SELECT COUNT( * ) FROM t1 GROUP BY y *)
let simpleCountQuery2 =
	RAProject (RARenameCol ("c", "x", RAAggregate (RANewColumn (RATable "t1", "c", RAXoper (OPIntConst 1, [])), ["y"], [("c", AGSum)])), ["x"; "y"]);;	

(* SELECT y, COUNT( * ) FROM t1 where 2 * x<y GROUP BY y *)
let simpleCountQuery3 =
	RAProject (RARenameCol ("c", "x", RAAggregate (RANewColumn (RAFilter (RATable "t1", RAXoper (OPLessThan, [RAXoper (OPMult,[RAXoper (OPIntConst 2,[]); RAXattribute "x"]); RAXattribute "y"]) ), "c", RAXoper (OPIntConst 1, [])), ["y"], [("c", AGCount)])), ["x"; "y"]);;	

let orig_aiddistrQuery =
let earliest_arrival ship_lat ship_long port_lat port_long max_speed =
    RAXoper (OPCeiling, [RAXoper (OPDiv, [RAXoper (OPGeoDist, [RAXattribute ship_lat; RAXattribute ship_long; RAXattribute port_lat; RAXattribute port_long]); RAXattribute max_speed])])
in
RALetExp ("compute_reachable_ports",
  RARenameCol("port.port_id", "port_id",
  RARenameCol("arrival", "arrival",
    RAProject(
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("longitude", "ship.longitude",
          RARenameCol("latitude", "ship.latitude",
          RARenameCol("maxspeed", "ship.maxspeed",
          RARenameCol("name", "ship.name",
            RATable "ship"
          ))));
          RARenameCol("longitude", "port.longitude",
          RARenameCol("latitude", "port.latitude",
          RARenameCol("port_id", "port.port_id",
            RATable "port"
          )));
          RARenameCol("deadline", "parameters.deadline",
          RARenameCol("shipname", "parameters.shipname",
            RATable "parameters"
          ))
        ],
        RAXoper (OPAnd, [RAXoper (OPLessEqual, [earliest_arrival "ship.longitude" "ship.latitude" "port.longitude" "port.latitude" "ship.maxspeed"; RAXattribute "parameters.deadline"]); RAXoper (OPIsEq, [RAXattribute "ship.name"; RAXattribute "parameters.shipname"]); RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "port.port_id"])])
      ),
     "arrival", earliest_arrival "ship.longitude" "ship.latitude" "port.longitude" "port.latitude" "ship.maxspeed"),
      ["port.port_id"; "arrival"])
  )),
RALetExp ("reachable_ports",  RARenameCol("rports.port_id", "port_id",
  RARenameCol("rports.arrival", "arrival",
    RAProject(
      RACartesian[
          RARenameCol("deadline", "p.deadline",
          RARenameCol("shipname", "p.shipname",
            RATable "parameters"
          ));
          RARenameCol("port_id", "rports.port_id",
          RARenameCol("arrival", "rports.arrival",
            RATable "compute_reachable_ports"
          ))
      ],
      ["rports.port_id"; "rports.arrival"])
  )),
RALetExp ("compute_feasible_ports",
  RARenameCol("port.port_id", "port_id",
    RAProject(
      RAFilter (
        RACartesian [
          RARenameCol("port_id", "reachable_ports.port_id",
            RATable "reachable_ports"
          );
          RARenameCol("port_id", "port.port_id",
          RARenameCol("available", "port.available",
          RARenameCol("harbordepth", "port.harbordepth",
          RARenameCol("offloadcapacity", "port.offloadcapacity",
            RATable "port"
          ))));
          RARenameCol("draft", "ship.draft",
          RARenameCol("cargo", "ship.cargo",
          RARenameCol("name", "ship.name",
            RATable "ship"
          )));
          RARenameCol("shipname", "parameters.shipname",
            RATable "parameters"
          )
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "reachable_ports.port_id"; RAXattribute "port.port_id"]); RAXattribute "port.available"; RAXoper (OPGreaterEqual, [RAXattribute "port.harbordepth"; RAXattribute "ship.draft"]); RAXoper (OPGreaterEqual, [RAXattribute "port.offloadcapacity"; RAXattribute "ship.cargo"]); RAXoper (OPIsEq, [RAXattribute "ship.name"; RAXattribute "parameters.shipname"])])
      ),
      ["port.port_id"])
  ),
RALetExp ("feasible_ports",  RARenameCol("fports.port_id", "port_id",
    RAProject(
      RACartesian[
          RARenameCol("shipname", "p.shipname",
            RATable "parameters"
          );
          RARenameCol("port_id", "fports.port_id",
            RATable "compute_feasible_ports"
          )
      ],
      ["fports.port_id"])
  ),
RALetExp ("slot1",
  RAAddSortColumn (
  RARenameCol("slot.port_id", "port_id",
  RARenameCol("slot.berth_id", "berth_id",
  RARenameCol("slot.slotstart", "slotstart",
  RARenameCol("slot.slotend", "slotend",
    RAProject(
          RARenameCol("port_id", "slot.port_id",
          RARenameCol("berth_id", "slot.berth_id",
          RARenameCol("slotstart", "slot.slotstart",
          RARenameCol("slotend", "slot.slotend",
            RATable "slot"
          )))),
      ["slot.port_id"; "slot.berth_id"; "slot.slotstart"; "slot.slotend"])
  )))),
    "row_id", ["port_id"; "berth_id"], "slotstart"),
RALetExp ("available_slots",
  RAAddSortColumn (
  RARenameCol("port_id", "port_id",
  RARenameCol("berth_id", "berth_id",
  RARenameCol("gap", "gap",
  RARenameCol("slotstart", "slotstart",
  RARenameCol("slotend", "slotend",
    RAProject(
    RANewColumn (
    RANewColumn (
    RANewColumn (
    RANewColumn (
    RANewColumn (
      RAFilter (
        (fullouterjoin
          (
          RARenameCol("slotend", "slot1.slotend",
          RARenameCol("port_id", "slot1.port_id",
          RARenameCol("berth_id", "slot1.berth_id",
          RARenameCol("row_id", "slot1.row_id",
            RATable "slot1"
          )))))
          (
          RARenameCol("slotstart", "slot2.slotstart",
          RARenameCol("port_id", "slot2.port_id",
          RARenameCol("berth_id", "slot2.berth_id",
          RARenameCol("row_id", "slot2.row_id",
            RATable "slot1"
          )))))
          (RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "slot1.port_id"; RAXattribute "slot2.port_id"]); RAXoper (OPIsEq, [RAXattribute "slot1.berth_id"; RAXattribute "slot2.berth_id"]); RAXoper (OPIsEq, [RAXoper (OPPlus, [RAXattribute "slot1.row_id"; RAXoper (OPIntConst 1, [])]); RAXattribute "slot2.row_id"])]))),
        RAXoper (OPLessThan, [RAXoper (OPCoalesce, [RAXattribute "slot1.slotend"; RAXoper (OPIntConst 0, [])]); RAXoper (OPCoalesce, [RAXattribute "slot2.slotstart"; RAXoper (OPIntConst 30, [])])])
      ),
     "slotend", RAXoper (OPCoalesce, [RAXattribute "slot2.slotstart"; RAXoper (OPIntConst 30, [])])),
     "slotstart", RAXoper (OPCoalesce, [RAXattribute "slot1.slotend"; RAXoper (OPIntConst 0, [])])),
     "gap", RAXoper (OPCoalesce, [RAXattribute "slot1.slotend"; RAXattribute "slot2.slotstart"])),
     "berth_id", RAXoper (OPCoalesce, [RAXattribute "slot1.berth_id"; RAXattribute "slot2.berth_id"])),
     "port_id", RAXoper (OPCoalesce, [RAXattribute "slot1.port_id"; RAXattribute "slot2.port_id"])),
      ["port_id"; "berth_id"; "gap"; "slotstart"; "slotend"])
  ))))),
    "slot_id", ["port_id"; "berth_id"], "gap"),
RALetExp ("slot_assignment",  RARenameCol("port.port_id", "port_id",
  RARenameCol("availslot.berth_id", "berth_id",
  RARenameCol("availslot.slot_id", "slot_id",
  RARenameCol("offloadstart", "offloadstart",
    RAProject(
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("port_id", "port.port_id",
          RARenameCol("offloadtime", "port.offloadtime",
            RATable "port"
          ));
          RARenameCol("port_id", "fport.port_id",
            RATable "feasible_ports"
          );
          RARenameCol("port_id", "rport.port_id",
          RARenameCol("arrival", "rport.arrival",
            RATable "reachable_ports"
          ));
          RARenameCol("port_id", "berth.port_id",
          RARenameCol("berth_id", "berth.berth_id",
          RARenameCol("berthlength", "berth.berthlength",
            RATable "berth"
          )));
          RARenameCol("port_id", "availslot.port_id",
          RARenameCol("berth_id", "availslot.berth_id",
          RARenameCol("slotstart", "availslot.slotstart",
          RARenameCol("slotend", "availslot.slotend",
          RARenameCol("slot_id", "availslot.slot_id",
            RATable "available_slots"
          )))));
          RARenameCol("name", "ship.name",
          RARenameCol("length", "ship.length",
            RATable "ship"
          ));
          RARenameCol("shipname", "parameters.shipname",
          RARenameCol("deadline", "parameters.deadline",
            RATable "parameters"
          ))
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "fport.port_id"]); RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "rport.port_id"]); RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "availslot.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "availslot.berth_id"; RAXattribute "berth.berth_id"]); RAXoper (OPIsEq, [RAXattribute "ship.name"; RAXattribute "parameters.shipname"]); RAXoper (OPGreaterEqual, [RAXattribute "berth.berthlength"; RAXattribute "ship.length"]); RAXoper (OPLessEqual, [RAXattribute "rport.arrival"; RAXattribute "parameters.deadline"]); RAXoper (OPLessEqual, [RAXattribute "availslot.slotstart"; RAXattribute "parameters.deadline"]); RAXoper (OPLessEqual, [RAXoper (OPPlus, [RAXattribute "rport.arrival"; RAXattribute "port.offloadtime"]); RAXattribute "availslot.slotend"]); RAXoper (OPLessEqual, [RAXoper (OPPlus, [RAXattribute "availslot.slotstart"; RAXattribute "port.offloadtime"]); RAXattribute "availslot.slotend"])])
      ),
     "offloadstart", RAXoper (OPITE, [RAXoper (OPLessThan, [RAXattribute "rport.arrival"; RAXattribute "availslot.slotstart"]); RAXattribute "rport.arrival"; RAXattribute "availslot.slotstart"])),
      ["port.port_id"; "availslot.berth_id"; "availslot.slot_id"; "offloadstart"])
  )))),
  RAUnionWithDifferentSchema(RAUnionWithDifferentSchema(RATable "slot_assignment", RATable "feasible_ports"), RATable "reachable_ports")
)))))));;

let aiddistrDbdesc = orig_aiddistrDbdesc (* simpleCountDbdesc *);;

let aiddistrQuery = orig_aiddistrQuery (* simpleCountQuery3 *);;

