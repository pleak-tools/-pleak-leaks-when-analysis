open GrbGraphs;;
open GrbInput;;

let aiddistrDbdesc =
     RLMap.add "parameters"
    (RLMap.add "param_id" VUnit (RLMap.add "deadline" VInteger (RLMap.singleton "shipname" VString)), [RLSet.singleton "param_id"])
  (
  RLMap.add "port_1"
    (RLMap.add "port_id" VInteger (RLMap.add "name" VString (RLMap.add "latitude" VReal (RLMap.add "longitude" VReal (RLMap.add "offloadcapacity" VInteger (RLMap.add "offloadtime" VInteger (RLMap.add "harbordepth" VInteger (RLMap.singleton "available" VBoolean))))))), [RLSet.singleton "port_id"])
  (
  RLMap.add "ship_2"
    (RLMap.add "ship_id" VInteger (RLMap.add "name" VString (RLMap.add "cargo" VInteger (RLMap.add "latitude" VReal (RLMap.add "longitude" VReal (RLMap.add "length" VInteger (RLMap.add "draft" VInteger (RLMap.singleton "maxspeed" VInteger))))))), [RLSet.singleton "ship_id"])
  (
  RLMap.add "berth"
    (RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.singleton "berthlength" VInteger)), [RLSet.from_list ["port_id"; "berth_id"]])
  (
  RLMap.singleton "slot"
    (RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.add "slot_id" VInteger (RLMap.add "ship_id" VInteger (RLMap.add "slotstart" VInteger (RLMap.singleton "slotend" VInteger))))), [RLSet.from_list ["port_id"; "berth_id"; "slot_id"]])
  ))));;

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
RALetExp ("compute_reachable_ports",
  RARenameCol("port_2.port_id", "port_id",
  RARenameCol("ship_2.ship_id", "ship_id",
  RARenameCol("ship_2.name", "name",
  RARenameCol("ship_2.cargo", "cargo",
  RARenameCol("ship_2.draft", "draft",
  RARenameCol("arrival", "arrival",
    RAProject(
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("longitude", "ship_2.longitude",
          RARenameCol("latitude", "ship_2.latitude",
          RARenameCol("maxspeed", "ship_2.maxspeed",
          RARenameCol("name", "ship_2.name",
          RARenameCol("ship_id", "ship_2.ship_id",
          RARenameCol("cargo", "ship_2.cargo",
          RARenameCol("draft", "ship_2.draft",
            RATable "ship_2"
          )))))));
          RARenameCol("longitude", "port_2.longitude",
          RARenameCol("latitude", "port_2.latitude",
          RARenameCol("port_id", "port_2.port_id",
            RATable "port_2"
          )));
          RARenameCol("deadline", "parameters.deadline",
          RARenameCol("shipname", "parameters.shipname",
            RATable "parameters"
          ))
        ],
        RAXoper (OPAnd, [RAXoper (OPLessEqual, [earliest_arrival "ship_2.longitude" "ship_2.latitude" "port_2.longitude" "port_2.latitude" "ship_2.maxspeed"; RAXattribute "parameters.deadline"]); RAXoper (OPIsEq, [RAXattribute "ship_2.name"; RAXattribute "parameters.shipname"]); RAXoper (OPIsEq, [RAXattribute "port_2.port_id"; RAXattribute "port_2.port_id"])])
      ),
     "arrival", earliest_arrival "ship_2.longitude" "ship_2.latitude" "port_2.longitude" "port_2.latitude" "ship_2.maxspeed"),
      ["port_2.port_id"; "ship_2.ship_id"; "ship_2.name"; "ship_2.cargo"; "ship_2.draft"; "arrival"])
  )))))),
RALetExp ("reachable_ports_2",  RARenameCol("rports.port_id", "port_id",
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
RALetExp ("ship_requirements_2",  RARenameCol("rports.ship_id", "ship_id",
  RARenameCol("rports.name", "name",
  RARenameCol("rports.cargo", "cargo",
  RARenameCol("rports.draft", "draft",
    RAProject(
      RACartesian[
          RARenameCol("deadline", "p.deadline",
          RARenameCol("shipname", "p.shipname",
            RATable "parameters"
          ));
          RARenameCol("ship_id", "rports.ship_id",
          RARenameCol("name", "rports.name",
          RARenameCol("cargo", "rports.cargo",
          RARenameCol("draft", "rports.draft",
            RATable "compute_reachable_ports"
          ))))
      ],
      ["rports.ship_id"; "rports.name"; "rports.cargo"; "rports.draft"])
  )))),
RALetExp ("ship_requirements_1",  RARenameCol("ns2.ship_id", "ship_id",
  RARenameCol("ns2.name", "name",
  RARenameCol("ns2.cargo", "cargo",
  RARenameCol("ns2.draft", "draft",
    RAProject(
          RARenameCol("ship_id", "ns2.ship_id",
          RARenameCol("name", "ns2.name",
          RARenameCol("cargo", "ns2.cargo",
          RARenameCol("draft", "ns2.draft",
            RATable "ship_requirements_2"
          )))),
      ["ns2.ship_id"; "ns2.name"; "ns2.cargo"; "ns2.draft"])
  )))),
RALetExp ("reachable_ports_1",  RARenameCol("rp2.port_id", "port_id",
  RARenameCol("rp2.arrival", "arrival",
    RAProject(
          RARenameCol("port_id", "rp2.port_id",
          RARenameCol("arrival", "rp2.arrival",
            RATable "reachable_ports_2"
          )),
      ["rp2.port_id"; "rp2.arrival"])
  )),
RALetExp ("compute_feasible_ports",
  RARenameCol("port_2.port_id", "port_id",
    RAProject(
      RAFilter (
        RACartesian [
          RARenameCol("port_id", "reachable_ports_2.port_id",
            RATable "reachable_ports_2"
          );
          RARenameCol("port_id", "port_2.port_id",
          RARenameCol("available", "port_2.available",
          RARenameCol("harbordepth", "port_2.harbordepth",
          RARenameCol("offloadcapacity", "port_2.offloadcapacity",
            RATable "port_2"
          ))));
          RARenameCol("draft", "ship_2.draft",
          RARenameCol("cargo", "ship_2.cargo",
          RARenameCol("name", "ship_2.name",
            RATable "ship_2"
          )));
          RARenameCol("shipname", "parameters.shipname",
            RATable "parameters"
          )
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "reachable_ports_2.port_id"; RAXattribute "port_2.port_id"]); RAXattribute "port_2.available"; RAXoper (OPGreaterEqual, [RAXattribute "port_2.harbordepth"; RAXattribute "ship_2.draft"]); RAXoper (OPGreaterEqual, [RAXattribute "port_2.offloadcapacity"; RAXattribute "ship_2.cargo"]); RAXoper (OPIsEq, [RAXattribute "ship_2.name"; RAXattribute "parameters.shipname"])])
      ),
      ["port_2.port_id"])
  ),
RALetExp ("feasible_ports_1",  RARenameCol("fports.port_id", "port_id",
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
RALetExp ("feasible_ports_2",  RARenameCol("fp1.port_id", "port_id",
    RAProject(
          RARenameCol("port_id", "fp1.port_id",
            RATable "feasible_ports_1"
          ),
      ["fp1.port_id"])
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
RALetExp ("slot_assignment_2",  RARenameCol("port_2.port_id", "port_id",
  RARenameCol("availslot.berth_id", "berth_id",
  RARenameCol("availslot.slot_id", "slot_id",
  RARenameCol("offloadstart", "offloadstart",
    RAProject(
    RANewColumn (
      RAFilter (
        RACartesian [
          RARenameCol("port_id", "port_2.port_id",
          RARenameCol("offloadtime", "port_2.offloadtime",
            RATable "port_2"
          ));
          RARenameCol("port_id", "fport.port_id",
            RATable "feasible_ports_2"
          );
          RARenameCol("port_id", "rport.port_id",
          RARenameCol("arrival", "rport.arrival",
            RATable "reachable_ports_2"
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
          RARenameCol("name", "ship_2.name",
          RARenameCol("length", "ship_2.length",
            RATable "ship_2"
          ));
          RARenameCol("shipname", "parameters.shipname",
          RARenameCol("deadline", "parameters.deadline",
            RATable "parameters"
          ))
        ],
        RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port_2.port_id"; RAXattribute "fport.port_id"]); RAXoper (OPIsEq, [RAXattribute "port_2.port_id"; RAXattribute "rport.port_id"]); RAXoper (OPIsEq, [RAXattribute "port_2.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "availslot.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "availslot.berth_id"; RAXattribute "berth.berth_id"]); RAXoper (OPIsEq, [RAXattribute "ship_2.name"; RAXattribute "parameters.shipname"]); RAXoper (OPGreaterEqual, [RAXattribute "berth.berthlength"; RAXattribute "ship_2.length"]); RAXoper (OPLessEqual, [RAXattribute "rport.arrival"; RAXattribute "parameters.deadline"]); RAXoper (OPLessEqual, [RAXattribute "availslot.slotstart"; RAXattribute "parameters.deadline"]); RAXoper (OPLessEqual, [RAXoper (OPPlus, [RAXattribute "rport.arrival"; RAXattribute "port_2.offloadtime"]); RAXattribute "availslot.slotend"]); RAXoper (OPLessEqual, [RAXoper (OPPlus, [RAXattribute "availslot.slotstart"; RAXattribute "port_2.offloadtime"]); RAXattribute "availslot.slotend"])])
      ),
     "offloadstart", RAXoper (OPITE, [RAXoper (OPLessThan, [RAXattribute "rport.arrival"; RAXattribute "availslot.slotstart"]); RAXattribute "rport.arrival"; RAXattribute "availslot.slotstart"])),
      ["port_2.port_id"; "availslot.berth_id"; "availslot.slot_id"; "offloadstart"])
  )))),
RALetExp ("slot_assignment_1",  RARenameCol("sa2.port_id", "port_id",
  RARenameCol("sa2.berth_id", "berth_id",
  RARenameCol("sa2.slot_id", "slot_id",
  RARenameCol("sa2.offloadstart", "offloadstart",
    RAProject(
          RARenameCol("port_id", "sa2.port_id",
          RARenameCol("berth_id", "sa2.berth_id",
          RARenameCol("slot_id", "sa2.slot_id",
          RARenameCol("offloadstart", "sa2.offloadstart",
            RATable "slot_assignment_2"
          )))),
      ["sa2.port_id"; "sa2.berth_id"; "sa2.slot_id"; "sa2.offloadstart"])
  )))),
  RATable "slot_assignment_2"
)))))))))))));;
