open GrbGraphs;;
open GrbCommons;;

let dimmapToStrWithPref vpref bm = String.concat " " (Array.to_list (Array.map (fun idx -> vpref ^ (string_of_int idx)) bm));;

let idAndArgsToStrWithPref vpref nid bm = if Array.length bm > 0 then "(n" ^ (NewName.to_string nid) ^ " " ^ (dimmapToStrWithPref vpref bm) ^ ")" else "n" ^ (NewName.to_string nid);;


let writeOrderingToZ3 dg oc =
	let dimmapToStr = dimmapToStrWithPref "x"
	and idAndArgsToStr = idAndArgsToStrWithPref "x"
	in
	DG.foldnodes (fun n () ->
		if n.nkind.outputtype = VInteger then
		begin
			let (AITT nb) = n.outputindextype
			in
			let nbinps = String.concat " " (Array.to_list (Array.map (fun _ -> "Int") nb.(0)))
			in
			output_string oc ("(declare-fun n" ^ (NewName.to_string n.id) ^ " (" ^ nbinps ^ ") Int)\n")
		end
	) dg ();
	let toBeConnected = function
		| NNMaximum
		| NNTimePoint _
		| NNOperation (OPIntConst _) -> true
		| _ -> false
	in
	DG.foldnodes (fun n () ->
		if (n.nkind.outputtype = VInteger) && (toBeConnected n.nkind.nodeintlbl) then
		begin
			let (AITT na) = n.inputindextype
			and (AITT nb) = n.outputindextype
			and (IxM ncc) = n.ixtypemap
			in
			let qvarsNA = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " Int)") na.(0)))
			and needsForAll = (Array.length na.(0)) > 0
			in
			let Some (_, _, fwdmap) = ncc.(0)
			in
			match n.nkind.nodeintlbl with
			| NNMaximum ->
			begin
				DG.nodefoldedges (fun ((IxM cc,_),_,_) () ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					output_string oc "(assert ";
					if needsForAll then 
					begin
						output_string oc ("(forall (" ^ qvarsNA ^ ") ")
					end;
					output_string oc "(<= ";
					output_string oc (idAndArgsToStr srcid backmap);
					output_string oc " ";
					output_string oc (idAndArgsToStr n.id fwdmap);
					output_string oc ")";
					if needsForAll then begin output_string oc ")" end;
					output_string oc ")\n";
				) n ();
				output_string oc "(assert ";
				if needsForAll then 
				begin
					output_string oc ("(forall (" ^ qvarsNA ^ ") ")
				end;
				output_string oc "(or ";
				DG.nodefoldedges (fun ((IxM cc,_),_,_) () ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					output_string oc "(= ";
					output_string oc (idAndArgsToStr srcid backmap);
					output_string oc " ";
					output_string oc (idAndArgsToStr n.id fwdmap);
					output_string oc ") "
				) n ();
				output_string oc ")";
				if needsForAll then begin output_string oc ")" end;
				output_string oc ")\n"
			end
			| NNTimePoint _ ->
			begin
				output_string oc "(assert ";
				if needsForAll then 
				begin
					output_string oc ("(forall (" ^ qvarsNA ^ ") ")
				end;
				output_string oc "(< ";
				DG.nodefoldedges (fun ((IxM cc,_),_,prt) () ->
					if prt = (PortSingle VInteger) then
						let Some (srcid,_,backmap) = cc.(0)
						in
						output_string oc (idAndArgsToStr srcid backmap)
				) n ();
				output_string oc " ";
				output_string oc (idAndArgsToStr n.id fwdmap);
				output_string oc ")";
				if needsForAll then begin output_string oc ")" end;
				output_string oc ")\n"
			end
			| NNOperation (OPIntConst xx) ->
				output_string oc ("(assert (= " ^ (idAndArgsToStr n.id fwdmap) ^ " " ^ (string_of_int xx) ^ "))\n" )
		end
	) dg ()
;;

let writeBooleanDescToZ3 dg oc =
	let dimmapToStr = dimmapToStrWithPref "x"
	and idAndArgsToStr = idAndArgsToStrWithPref "x"
	in
	DG.foldnodes (fun n () ->
		if n.nkind.outputtype = VBoolean then
		begin
			let (AITT nb) = n.outputindextype
			in
			let nbinps = String.concat " " (Array.to_list (Array.map (fun _ -> "Int") nb.(0)))
			in
			output_string oc ("(declare-fun n" ^ (NewName.to_string n.id) ^ " (" ^ nbinps ^ ") Bool)\n")
		end
	) dg ();
	let toBeConnected = function
		| NNAnd
		| NNId
		| NNOr
		| NNLongOr
		| NNNot -> true
		| _ -> false
	in
	DG.foldnodes (fun n () ->
		if (n.nkind.outputtype = VBoolean) && (toBeConnected n.nkind.nodeintlbl) then
		begin
			let (AITT na) = n.inputindextype
			and (AITT nb) = n.outputindextype
			and (IxM ncc) = n.ixtypemap
			in
			let qvarsNA = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " Int)") na.(0)))
			and needsForAll = (Array.length na.(0)) > 0
			in
			let Some (_, _, fwdmap) = ncc.(0)
			in
			match n.nkind.nodeintlbl with
			| NNAnd
			| NNOr -> begin
				output_string oc "(assert ";
				if needsForAll then 
				begin
					output_string oc ("(forall (" ^ qvarsNA ^ ") ")
				end;
				output_string oc "(= (";
				output_string oc (match n.nkind.nodeintlbl with | NNAnd -> "and " | _ -> "or ");
				DG.nodefoldedges (fun ((IxM cc,_), _, _) () ->
					let Some (nprevid, _, backmap) = cc.(0)
					in
					output_string oc (idAndArgsToStr nprevid backmap);
					output_string oc " "
				) n ();
				output_string oc ") ";
				output_string oc (idAndArgsToStr n.id fwdmap);
				output_string oc ")";
				if needsForAll then (output_string oc ")");
				output_string oc ")\n"
			end
			| NNLongOr -> begin
				let backmappl = ref None
				and previdpl = ref None
				in
				DG.nodefoldedges (fun ((IxM cc,_), _, _) () ->
					let Some (nprevid, _, backmap) = cc.(0)
					in
					backmappl := Some backmap;
					previdpl := Some nprevid
				) n ();
				let Some backmap = !backmappl
				and Some previd = !previdpl
				in
				output_string oc "(assert ";
				output_string oc ("(forall (" ^ qvarsNA ^ ") ");
				output_string oc "(=> ";
				output_string oc (idAndArgsToStr previd backmap);
				output_string oc " ";
				output_string oc (idAndArgsToStr n.id fwdmap);
				output_string oc ")))\n";
				output_string oc "(assert ";
				output_string oc ("(forall (" ^ qvarsNA ^ ") ");
				output_string oc "(=> (not ";
				output_string oc (idAndArgsToStr n.id fwdmap);
				output_string oc ") (not ";
				output_string oc (idAndArgsToStr previd backmap);
				output_string oc "))))\n";
			end
			| NNId
			| NNNot -> begin
				let isNeg = match n.nkind.nodeintlbl with | NNId -> false | _ -> true
				in
				let backmappl = ref None
				and previdpl = ref None
				in
				DG.nodefoldedges (fun ((IxM cc,_), _, _) () ->
					let Some (nprevid, _, backmap) = cc.(0)
					in
					backmappl := Some backmap;
					previdpl := Some nprevid
				) n ();
				let Some backmap = !backmappl
				and Some previd = !previdpl
				in
				output_string oc "(assert ";
				output_string oc ("(forall (" ^ qvarsNA ^ ") ");
				output_string oc "(= ";
				output_string oc (idAndArgsToStr n.id fwdmap);
				output_string oc " ";
				(if isNeg then output_string oc "(not ");
				output_string oc (idAndArgsToStr previd backmap);
				(if isNeg then output_string oc ")");
				output_string oc ")))\n"
			end
		end
	) dg ()
;;

let askZ3ForRedundantEdges dg oc =
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	in
	DG.foldnodes (fun n () ->
		if n.nkind.nodeintlbl = NNAnd then
		begin
			let (AITT na) = n.inputindextype
			and (IxM ncc) = n.ixtypemap
			in
			let Some (_, _, fwdmap) = ncc.(0)
			in
			DG.nodefoldedges (fun ((IxM cc, testeid), _, _) () ->
				let Some (previd, _, backmap) = cc.(0)
				in
				output_string oc "(push)\n";
				output_string oc ("(echo \"Now testing the edge from v_" ^ (NewName.to_string previd) ^ " to v_" ^ (NewName.to_string n.id) ^ "...\")\n" );
				Array.iteri (fun idx _ ->
					output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () Int)\n")
				) na.(0);
				DG.nodefoldedges (fun ((IxM cc', othereid), _, _) () ->
					if othereid <> testeid then
					begin
						let Some (previd', _, backmap') = cc'.(0)
						in
						output_string oc "(assert ";
						output_string oc (idAndArgsToStr previd' backmap');
						output_string oc ")\n"
					end
				) n ();
				output_string oc "(assert (not ";
				output_string oc (idAndArgsToStr previd backmap);
				output_string oc "))\n";
				output_string oc "(check-sat)\n";
				output_string oc "(pop)\n"
			) n ()
		end
	) dg ()
;;

let askZ3ForRedundantMaxEdges dg0 oc =
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	in
	let currdg = ref dg0
	in
	output_string oc "(set-option :timeout 2000)\n";
	output_string oc "(reset)\n";
	writeOrderingToZ3 !currdg oc;
	let () = DG.foldnodes (fun n0 () ->
		if n0.nkind.nodeintlbl <> NNMaximum then () else
		let (AITT na) = n0.inputindextype
		and (IxM ncc) = n0.ixtypemap
		in
		let Some (_, _, fwdmap) = ncc.(0)
		in
		DG.nodefoldedges (fun ((IxM cc, eid), _, _) () ->
			let Some (previd, _, backmap) = cc.(0)
			in
			output_string oc "(push)\n";
			output_string oc ("(echo \"Now testing the edge from v_" ^ (NewName.to_string previd) ^ " to v_" ^ (NewName.to_string n0.id) ^ "...\")\n" );
			Array.iteri (fun idx _ ->
				output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () Int)\n")
			) na.(0);
			DG.nodefoldedges (fun ((IxM cc',eid'),_,_) () ->
				if eid = eid' then () else
				let Some (previd',_,backmap') = cc'.(0)
				in
				output_string oc "(assert (";
				output_string oc (if eid < eid' then "< " else "<= ");
				output_string oc (idAndArgsToStr previd' backmap');
				output_string oc " ";
				output_string oc (idAndArgsToStr previd backmap);
				output_string oc "))\n"
			) n0 ();
			output_string oc "(check-sat)\n";
			output_string oc "(pop)\n"
			) n0 ()
		) !currdg ()
		in
	output_string oc "(exit)\n";
	flush oc
;;

let removeRedundantMaxEdges dg0 =
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	in
	let currdg = ref dg0
	and runagain = ref true
	and (ic,oc) = Unix.open_process "z3 -in"
	in
	output_string oc "(set-option :timeout 2000)\n";
	while !runagain do
		runagain := false;
		output_string oc "(reset)\n";
		writeOrderingToZ3 !currdg oc;
		let redundantEdges = DG.foldnodes (fun n0 fedgeset ->
			if n0.nkind.nodeintlbl <> NNMaximum then fedgeset else
			let (AITT na) = n0.inputindextype
			and (IxM ncc) = n0.ixtypemap
			in
			let Some (_, _, fwdmap) = ncc.(0)
			in
			DG.nodefoldedges (fun ((IxM cc, eid), _, _) ffedgeset ->
				let Some (previd, _, backmap) = cc.(0)
				in
				output_string oc "(push)\n";
				Array.iteri (fun idx _ ->
					output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () Int)\n")
				) na.(0);
				DG.nodefoldedges (fun ((IxM cc',eid'),_,_) () ->
					if eid = eid' then () else
					let Some (previd',_,backmap') = cc'.(0)
					in
					output_string oc "(assert (";
					output_string oc (if eid < eid' then "< " else "<= ");
					output_string oc (idAndArgsToStr previd' backmap');
					output_string oc " ";
					output_string oc (idAndArgsToStr previd backmap);
					output_string oc "))\n"
				) n0 ();
				output_string oc "(check-sat)\n";
				flush oc;
				let answer = input_line ic
				in
				output_string oc "(pop)\n";
				if answer = "unknown" then
				begin
					print_endline ("Could not figure out if max-input edge " ^ (NewName.to_string eid) ^ " is removable"); ffedgeset
				end
				else if answer = "unsat" then
					IdtSet.add eid ffedgeset
				else
					ffedgeset
			) n0 fedgeset
		) !currdg IdtSet.empty
		in
		if IdtSet.is_empty redundantEdges then
		begin
			runagain := false
		end
		else
		begin
			runagain := true;
			currdg := IdtSet.fold DG.remedge redundantEdges !currdg
		end
	done;
	output_string oc "(exit)\n";
	flush oc;
	ignore (Unix.close_process (ic,oc));
	!currdg
;;

let removeRedundantEdgesWithZ3 dg0 =
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	in
	let currdg = ref dg0
	and runagain = ref true
	and (ic,oc) = Unix.open_process "z3 -in"
	in
	output_string oc "(set-option :timeout 2000)\n";
	while !runagain do
		runagain := false;
		output_string oc "(reset)\n";
		writeBooleanDescToZ3 !currdg oc;
		let dgForIter = !currdg
		in
		DG.foldnodes (fun n0 () ->
			if n0.nkind.nodeintlbl = NNAnd then
			begin
				let changes = ref false
				and n = DG.findnode n0.id !currdg
				in
				let (AITT na) = n.inputindextype
				and (IxM ncc) = n.ixtypemap
				in
				let Some (_, _, fwdmap) = ncc.(0)
				in
				DG.nodefoldedges (fun ((IxM cc, testeid), _, _) () ->
					if not !changes then
					begin
						let Some (previd, _, backmap) = cc.(0)
						in
						output_string oc "(push)\n";
						Array.iteri (fun idx _ ->
							output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () Int)\n")
						) na.(0);
						DG.nodefoldedges (fun ((IxM cc', othereid), _, _) () ->
							if othereid <> testeid then
							begin
								let Some (previd', _, backmap') = cc'.(0)
								in
								output_string oc "(assert ";
								output_string oc (idAndArgsToStr previd' backmap');
								output_string oc ")\n"
							end
						) n ();
						output_string oc "(assert (not ";
						output_string oc (idAndArgsToStr previd backmap);
						output_string oc "))\n";
						output_string oc "(check-sat)\n";
						flush oc;
						let answer = input_line ic
						in
						if answer = "unknown" then
						begin
							print_endline ("Could not figure out if edge " ^ (NewName.to_string testeid) ^ " is removable")
						end;
						if answer = "unsat" then
						begin
							changes := true;
							runagain := true;
							currdg := DG.remedge testeid !currdg
						end;
						output_string oc "(pop)\n";
					end
				) n ()
			end
		) dgForIter ()
	done;
	output_string oc "(exit)\n";
	flush oc;
	ignore (Unix.close_process (ic,oc));
	!currdg
;;

