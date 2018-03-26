open GrbGraphs;;
open GrbInput;;

(*
let dbdesc =
	RLMap.add "persons" 
		(RLMap.add "id" VInteger (RLMap.add "name" VString (RLMap.add "dob" VInteger (RLMap.singleton "salary" VInteger))), [RLSet.singleton "id"])
	(
	RLMap.add "events" 
		(RLMap.add "eid" VInteger (RLMap.add "desc" VString (RLMap.singleton "year" VInteger)), [RLSet.singleton "eid"])
	RLMap.empty
	);;

let query =
	RAProject (
		RAFilter (RACartesian [RATable "persons"; RATable "events"],
			RAXoper (OPIsEq, [RAXattribute "dob"; RAXattribute "year"])),
		["id"; "name"; "eid"; "desc"]);;
*)

let aiddistrDbdesc =
	RLMap.add "parameters"
		(RLMap.add "pm_idx" VUnit (RLMap.add "shipname" VString (RLMap.singleton "deadline" VInteger)), [RLSet.singleton "pm_idx"])
	(
	RLMap.add "ship"
		(RLMap.add "ship_id" VInteger (RLMap.add "name" VString (RLMap.add "cargo" VInteger (RLMap.add "latitude" VReal (RLMap.add "longitude" VReal (RLMap.add "length" VInteger (RLMap.add "draft" VInteger (RLMap.singleton "speed" VInteger))))))), [RLSet.singleton "ship_id"; RLSet.singleton "name"])
	(
	RLMap.add "port"
		(RLMap.add "port_id" VInteger (RLMap.add "name" VString (RLMap.add "latitude" VReal (RLMap.add "longitude" VReal (RLMap.add "offloadcapacity" VInteger (RLMap.add "offloadtime" VInteger (RLMap.add "harbordepth" VInteger (RLMap.singleton "available" VBoolean))))))), [RLSet.singleton "port_id"])
	(
	RLMap.add "berth"
		(RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.singleton "berthlength" VInteger)), [RLSet.from_list ["port_id"; "berth_id"]])
	(
	RLMap.singleton "slot"
		(RLMap.add "port_id" VInteger (RLMap.add "berth_id" VInteger (RLMap.add "slot_id" VInteger (RLMap.add "ship_id" VInteger (RLMap.add "slotstart" VInteger (RLMap.singleton "slotend" VInteger))))), [RLSet.from_list ["port_id"; "berth_id"; "slot_id"]])
	))));;

let renameTableCols renamepairs tablename =
	List.fold_right (fun (oldname, newname) tbl -> RARenameCol (oldname, newname, tbl)) renamepairs (RATable tablename);;

let aiddistrQuery =
	let computearrival shiplat shiplong portlat portlong shipspeed =
		RAXoper (OPDiv, [RAXoper (OPGeoDist, [RAXattribute shiplat; RAXattribute shiplong; RAXattribute portlat; RAXattribute portlong]); RAXattribute shipspeed])
	in
	RALetExp ("reachable_ports",
		RAProject (
			RAFilter (
				RANewColumn (
					RACartesian [RATable "parameters"; renameTableCols [("name","ship.name")] "ship"; renameTableCols [("longitude", "port.longitude"); ("latitude", "port.latitude")] "port"],
					"rp_arrival",
					computearrival "latitude" "longitude" "port.latitude" "port.longitude" "speed" ),
				RAXoper (OPAnd, [RAXoper (OPLessEqual, [RAXattribute "rp_arrival"; RAXattribute "deadline"]); RAXoper (OPIsEq, [RAXattribute "ship.name"; RAXattribute "shipname"])])),
			["port_id"; "rp_arrival"]) ,
		RALetExp ("feasible_ports",

			RAProject (
				RANewColumn (
					RAFilter (
						RACartesian [RARenameCol ("port_id", "rport.port_id", RATable "reachable_ports"); renameTableCols [("longitude", "port.longitude"); ("latitude", "port.latitude")] "port"; RARenameCol ("name", "ship.name", RATable "ship"); RATable "parameters"],
						RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port_id"; RAXattribute "rport.port_id"]); RAXoper (OPIsEq, [RAXattribute "ship.name"; RAXattribute "shipname"]); RAXattribute "available"; RAXoper (OPGreaterEqual, [RAXattribute "harbordepth"; RAXattribute "draft"]); RAXoper (OPGreaterEqual ,[RAXattribute "offloadcapacity"; RAXattribute "cargo"])])),
						"fp_arrival" ,
						computearrival "latitude" "longitude" "port.latitude" "port.longitude" "speed" ),
				["port_id"; "name"; "fp_arrival"]),

			RALetExp ("available_slots",
				RAProject (
					RALetExp ("slot1",
						RAAddSortColumn (
							RAProject (RATable "slot", ["port_id"; "berth_id"; "slotstart"; "slotend"]),
							"row_id", ["port_id"; "berth_id"], "slotstart" ),
						RAAddSortColumn (
						RANewColumn (
						RANewColumn (
						RANewColumn (
						RANewColumn (
						RANewColumn (
						RAFilter (
							fullouterjoin_eqOfAttrs
								(RANewColumn (renameTableCols [("port_id","slot1.port_id"); ("berth_id","slot1.berth_id"); ("row_id","slot1.row_id"); ("slotstart", "slot1.slotstart"); ("slotend", "slot1.slotend")] "slot1", "rowidPlusOne", RAXoper (OPPlus, [RAXattribute "slot1.row_id"; RAXoper (OPIntConst 1, [])])))
								(renameTableCols [("port_id","slot2.port_id"); ("berth_id","slot2.berth_id"); ("row_id","slot2.row_id"); ("slotstart", "slot2.slotstart"); ("slotend", "slot2.slotend")] "slot1")
								[("slot1.port_id", "slot2.port_id"); ("slot1.berth_id", "slot2.berth_id"); ("rowidPlusOne", "slot2.row_id")],
							RAXoper (OPLessThan, [RAXoper (OPCoalesce, [RAXattribute "slot1.slotend"; RAXoper (OPIntConst 0, [])]); RAXoper (OPCoalesce, [RAXattribute "slot2.slotstart"; RAXoper (OPIntConst 30, [])])])
						),
						"port_id", RAXoper (OPCoalesce, [RAXattribute "slot1.port_id"; RAXattribute "slot2.port_id"]) ),
						"slotstart", RAXoper (OPCoalesce, [RAXattribute "slot1.slotend"; RAXoper (OPIntConst 0, [])]) ),
						"slotend", RAXoper (OPCoalesce, [RAXattribute "slot2.slotstart"; RAXoper (OPIntConst 30, [])]) ),
						"berth_id", RAXoper (OPCoalesce, [RAXattribute "slot1.berth_id"; RAXattribute "slot2.berth_id"]) ),
						"slotmid", RAXoper (OPCoalesce, [RAXattribute "slot1.slotend"; RAXattribute "slot2.slotstart"]) ),
						"gap_id", ["port_id"; "berth_id"], "slotmid" )
					) ,
					["port_id"; "berth_id"; "slotstart"; "slotend"; "gap_id"]),
				RALetExp ("slot_assignments",
					RAProject (
						RARenameCol ("port.port_id", "port_id", RARenameCol ("berth.berth_id", "berth_id",
						RAFilter (
							RANewColumn (
								RACartesian [
									renameTableCols [("port_id", "port.port_id"); ("offloadtime", "port.offloadtime")] "port";
									renameTableCols [("rp_arrival", "rport.arrival"); ("port_id", "rport.port_id")] "reachable_ports";
									renameTableCols [("port_id", "fport.port_id")] "feasible_ports";
									renameTableCols [("berth_id", "availslot.berth_id"); ("slotstart", "availslot.slotstart"); ("slotend", "availslot.slotend"); ("port_id", "availslot.port_id")] "available_slots";
									renameTableCols [("port_id", "berth.port_id"); ("berth_id", "berth.berth_id"); ("berthlength", "berth.berthlength")] "berth";
									renameTableCols [("name", "ship.name"); ("length", "ship.length")] "ship";
									RATable "parameters"
								] ,
								"offloadstart", RAXoper (OPITE, [RAXoper (OPLessThan, [RAXattribute "availslot.slotstart"; RAXattribute "rport.arrival"]); RAXattribute "rport.arrival"; RAXattribute "availslot.slotstart"])),
							RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "fport.port_id"]); RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "rport.port_id"]); RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "availslot.port_id"; RAXattribute "berth.port_id"]); RAXoper (OPIsEq, [RAXattribute "availslot.berth_id"; RAXattribute "berth.berth_id"]); RAXoper (OPIsEq, [RAXattribute "ship.name"; RAXattribute "shipname"]); RAXoper (OPGreaterEqual, [RAXattribute "berth.berthlength"; RAXattribute "ship.length"]); RAXoper (OPGreaterEqual, [RAXattribute "deadline"; RAXattribute "rport.arrival"]); RAXoper (OPGreaterEqual, [RAXattribute "deadline"; RAXattribute "availslot.slotstart"]); RAXoper (OPGreaterEqual, [RAXattribute "availslot.slotend"; RAXoper (OPPlus, [RAXattribute "rport.arrival"; RAXattribute "port.offloadtime"])]); RAXoper (OPGreaterEqual, [RAXattribute "availslot.slotend"; RAXoper (OPPlus, [RAXattribute "availslot.slotstart"; RAXattribute "port.offloadtime"])])])
						) ) ),
						["port_id"; "berth_id"; "offloadstart"]),
						RALetExp ("stepA",
							RAProject (
								RANewColumn (
									RAFilter (
										RACartesian [RARenameCol ("port_id", "stepA.port_id", RATable "reachable_ports"); renameTableCols [("name", "stepA.portname"); ("longitude", "port.longitude"); ("latitude", "port.latitude")] "port"; RATable "ship"; RATable "parameters"],
										RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port_id"; RAXattribute "stepA.port_id"]); RAXoper (OPIsEq, [RAXattribute "name"; RAXattribute "shipname"])]) ),
									"qa_arrival",
									computearrival "latitude" "longitude" "port.latitude" "port.longitude" "speed"),
								["stepA.port_id"; "stepA.portname"; "qa_arrival"]),
							RALetExp ("stepB",
								RAProject (
									RAFilter (
										RACartesian [RATable "feasible_ports"; renameTableCols [("port_id", "stepB.port_id"); ("name", "stepB.portname")] "port"],
										RAXoper (OPIsEq, [RAXattribute "port_id"; RAXattribute "stepB.port_id"]) ),
									["stepB.port_id"; "stepB.portname"]),
								RALetExp ("stepC",
									RAProject (
										RAFilter (
											RACartesian [
												renameTableCols [("port_id", "assign.port_id")] "slot_assignments";
												renameTableCols [("port_id", "rport.port_id")] "reachable_ports";
												renameTableCols [("port_id", "port.port_id"); ("name", "stepC.portname")] "port"
											] ,
											RAXoper (OPAnd, [RAXoper (OPIsEq, [RAXattribute "port.port_id"; RAXattribute "assign.port_id"]); RAXoper (OPIsEq, [RAXattribute "assign.port_id"; RAXattribute "rport.port_id"])])
										) ,
										["assign.port_id"; "stepC.portname"; "berth_id"; "rp_arrival"; "offloadstart"; "offloadtime"] ),
									RAUnionWithDifferentSchema (RAUnionWithDifferentSchema (RATable "stepA", RATable "stepB"), RATable "stepC")  
(*									RATable "stepB" *)
								)
							)
						)
				)
			)
		)
	)
;;

