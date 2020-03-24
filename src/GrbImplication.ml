open GrbGraphs;;
open GrbCommons;;

let dimmapToStrWithFun f bm = String.concat " " (Array.to_list (Array.map f bm));;

let dimmapToStrWithPref vpref = dimmapToStrWithFun (fun idx -> vpref ^ (string_of_int idx));;

let selIdAndArgsToStrWithFun npref f nid bm = if Array.length bm > 0 then "(" ^ npref ^ (NewName.to_string nid) ^ " " ^ (dimmapToStrWithFun f bm) ^ ")" else npref ^ (NewName.to_string nid);;

let selIdAndArgsToStrWithPref npref vpref nid bm = if Array.length bm > 0 then "(" ^ npref ^ (NewName.to_string nid) ^ " " ^ (dimmapToStrWithPref vpref bm) ^ ")" else npref ^ (NewName.to_string nid);;

let idAndArgsToStrWithFun f nid bm = selIdAndArgsToStrWithFun "n" f nid bm;;

let idAndArgsToStrWithPref vpref nid bm = selIdAndArgsToStrWithPref "n" vpref nid bm;;

let writeItAllToZ3 dg oc =
	let dimPrLoc = ref IdtSet.empty
	and anyChanges = ref true
	in
	while !anyChanges do
		anyChanges := false;
		DG.foldnodes (fun n () ->
			if IdtSet.mem n.id !dimPrLoc then () else
			let toAdd = match n.nkind.nodeintlbl with
				| NNTakeDim _
				| NNAddrGen _
				| NNTimePoint _ -> true
				| NNId
				| NNFilter _
				| NNITE _
				| NNMaximum
				| NNLongMerge _
				| NNMerge _ ->
					DG.nodefoldedges (fun ((IxM cc,_), _, prt) bb ->
						if bb then true else if (match prt with PortSingleB _ -> true | _ -> false) then false else
						let Some (srcid,_,_) = cc.(0)
						in IdtSet.mem srcid !dimPrLoc
					) n false
				| _ -> false
			in
			if toAdd then (anyChanges := true; dimPrLoc := IdtSet.add n.id !dimPrLoc) else ()
		) dg ()
	done;
	let dimProducers = !dimPrLoc
	in
	let dimmapToStr = dimmapToStrWithPref "x"
	and vIdAndArgsToStr = selIdAndArgsToStrWithPref "v" "x"
	and fIdAndArgsToStr = selIdAndArgsToStrWithPref "f" "x"
	in
	output_string oc "(declare-sort S)\n";
(*
"(declare-fun sord (S S) Bool)
(assert (forall ((x S) (y S)) (or (sord x y) (= x y) (sord y x))))
(assert (forall ((x S)) (not (sord x x))))
(assert (forall ((x S) (y S)) (=> (sord x y) (not (sord y x)))))
(assert (forall ((x S) (y S) (z S)) (=> (and (sord x y) (sord y z)) (sord x z))))\n";
*)
	DG.foldnodes (fun n () ->
		let (AITT nb) = n.outputindextype
		in
		let nbinps = String.concat " " (Array.to_list (Array.map (fun _ -> "S") nb.(0)))
		in
		let vType = if IdtSet.mem n.id dimProducers then "S" else if (n.nkind.outputtype = VBoolean) || (n.nkind.outputtype = VNaeloob) then "Bool" else "Int"
		in
		output_string oc ("(declare-fun f" ^ (NewName.to_string n.id) ^ " (" ^ nbinps ^ ") Bool)\n");
		output_string oc ("(declare-fun v" ^ (NewName.to_string n.id) ^ " (" ^ nbinps ^ ") " ^ vType ^ ")\n");
	) dg ();
	let addrgens = DG.foldnodes (fun n ll ->
		match n.nkind.nodeintlbl with
			| NNAddrGen (tag, dimnum, inpnum) ->
				let t = (tag, dimnum, inpnum)
				in
				if List.mem t ll then ll else t :: ll
			| _ -> ll
	) dg []
	in
	let addrFunName tag dimnum = "addrf_" ^ (NewName.to_string tag) ^ "_" ^ (string_of_int dimnum)
	in
	List.iter (fun (tag, dimnum, inpnum) ->
		let nbinps = Buffer.create 16
		and forallargs = Buffer.create 16
		and funargs = Buffer.create 16
		in
		for i = 1 to inpnum do
			Buffer.add_string nbinps "S";
			Buffer.add_string funargs ("x" ^ (string_of_int i));
			Buffer.add_string forallargs ("(x" ^ (string_of_int i) ^ " S)");
			if i < inpnum then (Buffer.add_string nbinps " "; Buffer.add_string forallargs " "; Buffer.add_string funargs " ") else ()
		done;
		output_string oc "(declare-fun ";
		output_string oc (addrFunName tag dimnum);
		output_string oc " (";
		Buffer.output_buffer oc nbinps;
		output_string oc ") S)\n";
(*		for i = 1 to inpnum do
			let invFunName = (addrFunName tag dimnum) ^ "_inv" ^ (string_of_int i)
			in
			output_string oc "(declare-fun ";
			output_string oc invFunName;
			output_string oc " (S) S)\n";
			output_string oc "(assert (forall (";
			Buffer.output_buffer oc forallargs;
			output_string oc (") (! (= x" ^ (string_of_int i));
			output_string oc (" (" ^ invFunName ^ " (" ^ (addrFunName tag dimnum) ^ " " );
			Buffer.output_buffer oc funargs;
			output_string oc ")))";
			output_string oc " :pattern (";
			output_string oc (" (" ^ (addrFunName tag dimnum) ^ " ");
			Buffer.output_buffer oc funargs;
			output_string oc ")) )))\n"
		done;
*)	) addrgens;
	DG.foldnodes (fun n () -> (* about the flow *)
		let (AITT na) = n.inputindextype
		and (AITT nb) = n.outputindextype
		and (IxM ncc) = n.ixtypemap
		in
		let qvarsNA = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " S)") na.(0)))
		and needsForAll = (Array.length na.(0)) > 0
		in
		let Some (_, _, fwdmap) = ncc.(0)
		in
		let output_forall_open () = if needsForAll then output_string oc ("(forall (" ^ qvarsNA ^ ") ") else ()
		and output_forall_close () = if needsForAll then output_string oc ")" else ()
		in
		match n.nkind.nodeintlbl with
			| NNFilter _
			| NNOutput _ ->
			begin
				let backmappl1 = ref None
				and previdpl1 = ref None
				and backmappl2 = ref None
				and previdpl2 = ref None
				in
				DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
					let Some (nprevid, _, backmap) = cc.(0)
					in
					if prt = PortSingleB true then
					begin
						backmappl1 := Some backmap;
						previdpl1 := Some nprevid
					end
					else
					begin
						backmappl2 := Some backmap;
						previdpl2 := Some nprevid
					end
				) n ();
				let Some backmapc = !backmappl1
				and Some previdc = !previdpl1
				and Some backmapv = !backmappl2
				and Some previdv = !previdpl2
				in
				output_string oc "(assert ";
				output_forall_open ();
				output_string oc "(=> ";
				output_string oc (fIdAndArgsToStr n.id fwdmap);
				output_string oc " (and ";
				output_string oc (fIdAndArgsToStr previdv backmapv);
				output_string oc " ";
				output_string oc (vIdAndArgsToStr previdc backmapc);
				output_forall_close ();
				output_string oc ")))\n"
			end
			| NNInput _
			| NNInputExists _ ->
			begin
				()
			end
			| _ ->
			begin
				let inpcount = DG.nodefoldedges (fun _ cnt -> cnt + 1) n 0
				in
				if inpcount = 0 then
				begin
					output_string oc "(assert ";
					output_forall_open ();
					output_string oc "(not ";
					output_string oc (fIdAndArgsToStr n.id fwdmap);
					output_forall_close ();
					output_string oc "))\n"
				end
				else
				begin
					output_string oc "(assert ";
					output_forall_open ();
					output_string oc "(=> ";
					output_string oc (fIdAndArgsToStr n.id fwdmap);
					output_string oc " (or ";
					DG.nodefoldedges (fun ((IxM cc, _), _, _) () ->
						let Some (nprevid, _, backmap) = cc.(0)
						in
						output_string oc (fIdAndArgsToStr nprevid backmap);
						output_string oc " "
					) n ();
					output_forall_close ();
					output_string oc ")))\n"
				end
			end
	) dg ();
	DG.foldnodes (fun n () -> (* about the values *)
		let (AITT na) = n.inputindextype
		and (AITT nb) = n.outputindextype
		and (IxM ncc) = n.ixtypemap
		in
		let qvarsNA = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " S)") na.(0)))
		and needsForAll = (Array.length na.(0)) > 0
		in
		let Some (_, _, fwdmap) = ncc.(0)
		in
		let output_forall_open () = if needsForAll then output_string oc ("(forall (" ^ qvarsNA ^ ") ") else ()
		and output_forall_close () = if needsForAll then output_string oc ")" else ()
		in
		match n.nkind.nodeintlbl with
		| NNAnd _
		| NNOr _ -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= (";
			output_string oc (match n.nkind.nodeintlbl with | NNAnd _ -> "and " | _ -> "or ");
			DG.nodefoldedges (fun ((IxM cc,_), _, _) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				output_string oc (vIdAndArgsToStr nprevid backmap);
				output_string oc " "
			) n ();
			output_string oc ") ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc ")";
			output_forall_close ();
			output_string oc ")\n"
		end
		| NNLongOr _ -> begin
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
			output_forall_open ();
			output_string oc "(=> ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc ")))\n";

			let qvarsNB = String.concat " " (Array.to_list (Array.map (fun idx -> "(x" ^ (string_of_int idx) ^ " S)" ) fwdmap))
			in
			let freeDims =
				let res = Array.make (Array.length na.(0)) true
				in
				Array.iter (fun x -> res.(x) <- false
				) fwdmap;
				res
			in
			let qvarsNAminusB = Buffer.create 16
			and isFirstInBuf = ref true
			in
			Array.iteri (fun idx b ->
				if b then
				begin
					(if not !isFirstInBuf then Buffer.add_char qvarsNAminusB ' ');
					isFirstInBuf := false;
					Buffer.add_string qvarsNAminusB "(x";
					Buffer.add_string qvarsNAminusB (string_of_int idx);
					Buffer.add_string qvarsNAminusB " S)"
				end else ()				
			) freeDims;
			let needsQA = (Array.length fwdmap) > 0
			and needsQE = (Array.length na.(0)) > (Array.length fwdmap)
			in
			output_string oc "(assert ";
			(if needsQA then output_string oc ("(forall (" ^ qvarsNB ^ ") "));
			(if needsQE then begin
				output_string oc "(exists (";
				Buffer.output_buffer oc qvarsNAminusB;
				output_string oc ") " end
			);
			output_string oc "(=> ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_string oc ")";
			(if needsQE then output_string oc ")");
			(if needsQA then output_string oc ")");
			output_string oc ")\n"
(*
			output_string oc "(assert ";
			output_string oc ("(forall (" ^ qvarsNA ^ ") ");
			output_string oc "(=> (not ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc ") (not ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_forall_close ();
			output_string oc ")))\n";
*)		end
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
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			(if isNeg then output_string oc "(not ");
			output_string oc (vIdAndArgsToStr previd backmap);
			(if isNeg then output_string oc ")");
			output_string oc ")))\n"
		end
		| NNTakeDim _ -> begin
			output_string oc "(assert ";
			output_string oc ("(forall (" ^ qvarsNA ^ ") ");
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc "x0";
			output_string oc ")))\n"
		end
		| NNFilter _ -> begin
			let backmappl = ref None
			and previdpl = ref None
			in
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				if prt = PortSingleB true then () else
				let Some (nprevid, _, backmap) = cc.(0)
				in
				backmappl := Some backmap;
				previdpl := Some nprevid
			) n ();
			let Some backmap = !backmappl
			and Some previd = !previdpl
			in
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_forall_close ();
			output_string oc "))\n"
		end
		| NNOperation OPPlus
		| NNSum -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc "(+ ";
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				output_string oc (vIdAndArgsToStr nprevid backmap);
				output_string oc " ";
			) n ();
			output_forall_close ();
			output_string oc ")))\n"
		end
		| NNOperation OPMult -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc "(* ";
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				output_string oc (vIdAndArgsToStr nprevid backmap);
				output_string oc " ";
			) n ();
			output_forall_close ();
			output_string oc ")))\n"
		end
(*		| NNOperation c when (match c with OPLessThan | OPGreaterThan | OPLessEqual | OPGreaterEqual | OPIsEq -> true | _ -> false) -> begin
			let kw = (match c with
				| OPLessThan -> "<"
				| OPGreaterThan -> ">"
				| OPLessEqual -> "<="
				| OPGreaterEqual -> ">="
				| OPIsEq -> "="
			)
			in
			let backmappl1 = ref None
			and previdpl1 = ref None
			and backmappl2 = ref None
			and previdpl2 = ref None
			in
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				if prt = PortOperInput 1 then
				begin
					backmappl1 := Some backmap;
					previdpl1 := Some nprevid
				end
				else
				begin
					backmappl2 := Some backmap;
					previdpl2 := Some nprevid
				end
			) n ();
			let Some backmap1 = !backmappl1
			and Some previd1 = !previdpl1
			and Some backmap2 = !backmappl2
			and Some previd2 = !previdpl2
			in
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc ("(" ^ kw ^ " ");
			output_string oc (vIdAndArgsToStr previd1 backmap1);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previd2 backmap2);
			output_forall_close ();
			output_string oc ")))\n"
		end
*)(*		| NNIsEq -> begin
			let backmappl1 = ref None
			and previdpl1 = ref None
			and backmappl2 = ref None
			and previdpl2 = ref None
			in
			DG.nodefoldedges (fun ((IxM cc,_), _, _) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				if !backmappl1 = None then
				begin
					backmappl1 := Some backmap;
					previdpl1 := Some nprevid
				end
				else
				begin
					backmappl2 := Some backmap;
					previdpl2 := Some nprevid
				end
			) n ();
			let Some backmap1 = !backmappl1
			and Some previd1 = !previdpl1
			and Some backmap2 = !backmappl2
			and Some previd2 = !previdpl2
			in
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc ("(= ");
			output_string oc (vIdAndArgsToStr previd1 backmap1);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previd2 backmap2);
			output_forall_close ();
			output_string oc ")))\n"
		end
*)		| NNOperation (OPIntConst c) -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc (string_of_int c);
			output_forall_close ();
			output_string oc "))\n"
		end
		| NNITE _ -> begin
			let backmappli = ref None
			and previdpli = ref None
			and backmapplt = ref None
			and previdplt = ref None
			and backmapplf = ref None
			and previdplf = ref None
			in
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				if prt = PortSingleB true then
				begin
					backmappli := Some backmap;
					previdpli := Some nprevid
				end
				else if (match prt with PortTrue _ -> true | _ -> false) then
				begin
					backmapplt := Some backmap;
					previdplt := Some nprevid
				end
				else
				begin
					backmapplf := Some backmap;
					previdplf := Some nprevid
				end
			) n ();
			let Some backmapi = !backmappli
			and Some previdi = !previdpli
			and Some backmapt = !backmapplt
			and Some previdt = !previdplt
			and Some backmapf = !backmapplf
			and Some previdf = !previdplf
			in
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(=> ";
			output_string oc (vIdAndArgsToStr previdi backmapi);
			output_string oc " ";
			output_string oc ("(= ");
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previdt backmapt);
			output_forall_close ();
			output_string oc ")))\n";
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(=> (not ";
			output_string oc (vIdAndArgsToStr previdi backmapi);
			output_string oc ") ";
			output_string oc ("(= ");
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previdf backmapf);
			output_forall_close ();
			output_string oc ")))\n";
		end
		| NNAggregate c when (match c with AGMin | AGMax -> true | _ -> false) -> begin
			let sign1 = (match c with
				| AGMin -> ">="
				| AGMax -> "<="
			)
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
			output_forall_open ();
			output_string oc ("(" ^ sign1 ^ " ");
			output_string oc (vIdAndArgsToStr previd backmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_forall_close ();
			output_string oc "))\n";
		end
		| NNDimEq -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " (= x0 x1)";
			output_forall_close ();
			output_string oc "))\n"
		end
		| NNMaximum -> begin
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				output_string oc "(assert ";
				output_forall_open ();
				output_string oc ("(<= ");
				output_string oc (vIdAndArgsToStr nprevid backmap);
				output_string oc " ";
				output_string oc (vIdAndArgsToStr n.id fwdmap);
				output_forall_close ();
				output_string oc "))\n";
			) n ();
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(or ";
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (nprevid, _, backmap) = cc.(0)
				in
				output_string oc ("(= ");
				output_string oc (vIdAndArgsToStr nprevid backmap);
				output_string oc " ";
				output_string oc (vIdAndArgsToStr n.id fwdmap);
				output_string oc ")\n";
			) n ();
			output_forall_close ();
			output_string oc "))\n"
		end
		| NNLongMerge _ -> begin
			let qvarsNB = String.concat " " (Array.to_list (Array.map (fun idx -> "(x" ^ (string_of_int idx) ^ " S)" ) fwdmap))
			in
			let freeDims =
				let res = Array.make (Array.length na.(0)) true
				in
				Array.iter (fun x -> res.(x) <- false
				) fwdmap;
				res
			in
			let qvarsNAminusB = Buffer.create 16
			and isFirstInBuf = ref true
			in
			Array.iteri (fun idx b ->
				if b then
				begin
					(if not !isFirstInBuf then Buffer.add_char qvarsNAminusB ' ');
					isFirstInBuf := false;
					Buffer.add_string qvarsNAminusB "(x";
					Buffer.add_string qvarsNAminusB (string_of_int idx);
					Buffer.add_string qvarsNAminusB " S)"
				end else ()				
			) freeDims;
			let needsQA = (Array.length fwdmap) > 0
			and needsQE = (Array.length na.(0)) > (Array.length fwdmap)
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
			(if needsQA then output_string oc ("(forall (" ^ qvarsNB ^ ") "));
			(if needsQE then begin
				output_string oc "(exists (";
				Buffer.output_buffer oc qvarsNAminusB;
				output_string oc ") " end
			);
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_string oc ")";
			(if needsQE then output_string oc ")");
			(if needsQA then output_string oc ")");
			output_string oc ")\n"
		end
		| NNMerge _ -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(or ";
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				let Some (previd, _, backmap) = cc.(0)
				in
				output_string oc ("(= ");
				output_string oc (vIdAndArgsToStr previd backmap);
				output_string oc " ";
				output_string oc (vIdAndArgsToStr n.id fwdmap);
				output_string oc ")\n";
			) n ();
			output_forall_close ();
			output_string oc "))\n"
		end
		| NNAddrGen (tag, dimnum, inpnum) -> begin
			let backmaps = Array.make inpnum [||]
			and previds = Array.make inpnum NewName.invalid_id
			in
			DG.nodefoldedges (fun ((IxM cc,_), _, prt) () ->
				match prt with
				| PortOperInput ac ->
					let Some (nprevid, _, backmap) = cc.(0)
					in
					backmaps.(ac - 1) <- backmap;
					previds.(ac - 1) <- nprevid
			) n ();
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc " (";
			output_string oc (addrFunName tag dimnum);
			for i = 1 to inpnum do
				output_string oc " ";
				output_string oc (vIdAndArgsToStr previds.(i-1) backmaps.(i-1))
			done;
			output_forall_close ();
			output_string oc ")))\n"
		end
		| _ -> ()
	) dg ()
;;	

let writeOrderingToZ3 dg oc =
	let dimmapToStr = dimmapToStrWithPref "x"
	and idAndArgsToStr = idAndArgsToStrWithPref "x"
	in
	DG.foldnodes (fun n () ->
		if n.nkind.outputtype = VTimePoint then
		begin
			let (AITT nb) = n.outputindextype
			in
			let nbinps = String.concat " " (Array.to_list (Array.map (fun _ -> "S") nb.(0)))
			in
			output_string oc ("(declare-fun n" ^ (NewName.to_string n.id) ^ " (" ^ nbinps ^ ") Int)\n")
		end
	) dg ();
	let toBeConnected = function
		| NNMaximum
		| NNTimePoint _
		| NNZeroTimePoint
		| NNOperation (OPTimePointConst _) -> true
		| _ -> false
	in
	DG.foldnodes (fun n () ->
		if (n.nkind.outputtype = VTimePoint) && (toBeConnected n.nkind.nodeintlbl) then
		begin
			let (AITT na) = n.inputindextype
			and (AITT nb) = n.outputindextype
			and (IxM ncc) = n.ixtypemap
			in
			let qvarsNA = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " S)") na.(0)))
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
					if prt = (PortSingle VTimePoint) then
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
			| NNZeroTimePoint ->
				output_string oc ("(assert (= " ^ (idAndArgsToStr n.id fwdmap) ^ " 0))\n" )
			| NNOperation (OPTimePointConst (Left xx)) | NNOperation (OPTimePointConst (Right xx)) ->
				output_string oc ("(assert (= " ^ (idAndArgsToStr n.id fwdmap) ^ " " ^ (string_of_int xx) ^ "))\n" )
		end
	) dg ()
;;

let makeAddrFunAppl afarg aflst =
	let rec wF afarg = function
	| [] -> afarg
	| (x::xs) -> wF ("(" ^ (match x with Left _ -> "af_" | Right _ -> "bf_") ^ (match x with Left (y,z) | Right (y,z) -> (NewName.to_string y) ^ "_" ^ (string_of_int z)) ^ " " ^ afarg ^ ")") xs
	in
	wF afarg (List.rev aflst)
;;

let writeBooleanDescToZ3 dg oc dimEqInformation =
	let dimmapToStr = dimmapToStrWithPref "x"
	and idAndArgsToStr = idAndArgsToStrWithPref "x"
	and extractDimEqInformation nid = match dimEqInformation with
		| None -> None
		| Some foundDeps ->
		try
			let pp = Hashtbl.find foundDeps nid
			in
			Some pp
		with Not_found -> None
	in
	DG.foldnodes (fun n () ->
		if (n.nkind.outputtype = VBoolean) || (n.nkind.outputtype = VNaeloob) then
		begin
			let (AITT nb) = n.outputindextype
			in
			let nbinps = String.concat " " (Array.to_list (Array.map (fun _ -> "S") nb.(0)))
			in
			output_string oc ("(declare-fun n" ^ (NewName.to_string n.id) ^ " (" ^ nbinps ^ ") Bool)\n")
		end
	) dg ();
	(if (match dimEqInformation with Some _ -> true | None -> false) then
	DG.foldnodes (fun n () ->
		match n.nkind.nodeintlbl with
			| NNAddrGen (x,y,z) when z=1 ->
			begin
				output_string oc ("(declare-fun af_" ^ (NewName.to_string x) ^ "_" ^ (string_of_int y) ^ " (S) S)\n");
				output_string oc ("(declare-fun bf_" ^ (NewName.to_string x) ^ "_" ^ (string_of_int y) ^ " (S) S)\n");
				output_string oc ("(assert (forall ((y S) (z S)) (= (= (af_" ^ (NewName.to_string x) ^ "_" ^ (string_of_int y) ^ " y) z) (= y (bf_" ^ (NewName.to_string x) ^ "_" ^ (string_of_int y) ^ " z)))))\n")
			end
			| _ -> ()
	) dg () );
	let toBeConnected = function
		| NNAnd _
		| NNId
		| NNOr _
		| NNLongOr _
		| NNLongAnd _
		| NNNotFlip _
		| NNNot -> true
		| _ -> false
	in
	DG.foldnodes (fun n () ->
		if ((n.nkind.outputtype = VBoolean) || (n.nkind.outputtype = VNaeloob)) && (toBeConnected n.nkind.nodeintlbl) then
		begin
			let (AITT na) = n.inputindextype
			and (AITT nb) = n.outputindextype
			and (IxM ncc) = n.ixtypemap
			in
			(match extractDimEqInformation n.id with
				| None -> ()
				| Some (_,outpEqs) ->
					let qvarsNB = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " S)") nb.(0)))
					and needsForAll = (Array.length nb.(0)) > 0
					in
					for leftDim = 0 to (Array.length nb.(0)) - 1 do for rightDim = 0 to (Array.length nb.(0)) - 1 do Hashtbl.iter (fun (lv,b) () ->
						if (leftDim = rightDim) && (lv = []) then () else
						begin
							output_string oc ("(assert (forall (" ^ qvarsNB ^ ") (=> ");
							(if not b then output_string oc "(not ");
							output_string oc (idAndArgsToStr n.id (Array.init (Array.length nb.(0)) (fun i -> i)));
							(if not b then output_string oc ")");
							output_string oc (" (= x" ^ (string_of_int leftDim) ^ " ");
							output_string oc (makeAddrFunAppl ("x" ^ (string_of_int rightDim)) lv);
							output_string oc "))))\n"
						end
					) outpEqs.(leftDim).(rightDim) done done
			);
			let qvarsNA = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " S)") na.(0)))
			and needsForAll = (Array.length na.(0)) > 0
			in
			let Some (_, _, fwdmap) = ncc.(0)
			in
			match n.nkind.nodeintlbl with
			| NNAnd _
			| NNOr _ -> begin
				output_string oc "(assert ";
				if needsForAll then 
				begin
					output_string oc ("(forall (" ^ qvarsNA ^ ") ")
				end;
				output_string oc "(= (";
				output_string oc (match n.nkind.nodeintlbl with | NNAnd _ -> "and " | _ -> "or ");
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
			| NNLongOr _
			| NNLongAnd _ -> begin
				let isLongOr = (match n.nkind.nodeintlbl with NNLongOr _ -> true | _ -> false)
				in
				let outputTwo s1 s2 = if isLongOr then output_string oc (s1 ^ " " ^ s2) else output_string oc (s2 ^ " " ^ s1)
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
				output_string oc "(=> ";
				outputTwo (idAndArgsToStr previd backmap) (idAndArgsToStr n.id fwdmap);
				output_string oc ")))\n";
				match extractDimEqInformation n.id with
					| None ->
					begin
						let qvarsNB = String.concat " " (Array.to_list (Array.map (fun idx -> "(x" ^ (string_of_int idx) ^ " S)" ) fwdmap))
						in
						let freeDims =
							let res = Array.make (Array.length na.(0)) true
							in
							Array.iter (fun x -> res.(x) <- false
							) fwdmap;
							res
						in
						let qvarsNAminusB = Buffer.create 16
						and isFirstInBuf = ref true
						in
						Array.iteri (fun idx b ->
							if b then
							begin
								(if not !isFirstInBuf then Buffer.add_char qvarsNAminusB ' ');
								isFirstInBuf := false;
								Buffer.add_string qvarsNAminusB "(x";
								Buffer.add_string qvarsNAminusB (string_of_int idx);
								Buffer.add_string qvarsNAminusB " S)"
							end else ()				
						) freeDims;
						let needsQA = (Array.length fwdmap) > 0
						and needsQE = (Array.length na.(0)) > (Array.length fwdmap)
						in
						output_string oc "(assert ";
						(if needsQA then output_string oc ("(forall (" ^ qvarsNB ^ ") "));
						(if needsQE then begin
							output_string oc "(exists (";
							Buffer.output_buffer oc qvarsNAminusB;
							output_string oc ") " end
						);
						output_string oc "(=> ";
						outputTwo (idAndArgsToStr n.id fwdmap) (idAndArgsToStr previd backmap);
						output_string oc ")";
						(if needsQE then output_string oc ")");
						(if needsQA then output_string oc ")");
						output_string oc ")\n"
					end
					| Some (inpEqs,outpEqs) ->
					begin
						let qvarsNB = String.concat " " (Array.to_list (Array.map (fun idx -> "(x" ^ (string_of_int idx) ^ " S)" ) fwdmap))
						in
						let invFwdMap =
							let res = Array.make (Array.length na.(0)) (-1)
							in
							Array.iteri (fun idx x -> res.(x) <- idx
							) fwdmap;
							res
						and invBackMap =
							let res = Array.make (Array.length na.(0)) (-1)
							in
							Array.iteri (fun idx x -> res.(x) <- idx
							) backmap;
							res
						in
						let freeDimVals = Array.init (Array.length na.(0)) (fun idx ->
							if invFwdMap.(idx) >= 0 then None else
							List.fold_right (fun sidx res ->
								match res with
								| Some _ -> res
								| None ->
									if (invFwdMap.(sidx) = (-1)) || (invBackMap.(sidx) = (-1)) then None else
									Hashtbl.fold (fun (lv,b) () res ->
										if (b && (not isLongOr)) || ((not b) && isLongOr) then res else
										match res with
										| Some _ -> res
										| None -> Some (sidx, lv)
									) inpEqs.(idx).(sidx) None
							) (intfromto 0 ((Array.length na.(0)) - 1)) None
						)
						in
						let qvarsNAminusB = Buffer.create 16
						and isFirstInBuf = ref true
						in
						Array.iteri (fun idx gg ->
							if (invFwdMap.(idx) = (-1)) && (gg = None) then
							begin
								(if not !isFirstInBuf then Buffer.add_char qvarsNAminusB ' ');
								isFirstInBuf := false;
								Buffer.add_string qvarsNAminusB "(x";
								Buffer.add_string qvarsNAminusB (string_of_int idx);
								Buffer.add_string qvarsNAminusB " S)"
							end else ()				
						) freeDimVals;
						let needsQA = (Array.length fwdmap) > 0
						and needsQE = not !isFirstInBuf
						in
						output_string oc "(assert ";
						(if needsQA then output_string oc ("(forall (" ^ qvarsNB ^ ") "));
						(if needsQE then begin
							output_string oc "(exists (";
							Buffer.output_buffer oc qvarsNAminusB;
							output_string oc ") " end
						);
						output_string oc "(=> ";
						let idAndArgsToStrSpecial = idAndArgsToStrWithFun (fun idx ->
							match freeDimVals.(idx) with
								| None -> "x" ^ (string_of_int idx)
								| Some (sidx, lv) -> makeAddrFunAppl ("x" ^ (string_of_int sidx)) lv
						)
						in
						outputTwo (idAndArgsToStr n.id fwdmap) (idAndArgsToStrSpecial previd backmap);
						output_string oc ")";
						(if needsQE then output_string oc ")");
						(if needsQA then output_string oc ")");
						output_string oc ")\n"
					end
			end
			| NNId
			| NNNot
			| NNNotFlip _ -> begin
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
				(if needsForAll then output_string oc ("(forall (" ^ qvarsNA ^ ") "));
				output_string oc "(= ";
				output_string oc (idAndArgsToStr n.id fwdmap);
				output_string oc " ";
				(if isNeg then output_string oc "(not ");
				output_string oc (idAndArgsToStr previd backmap);
				(if isNeg then output_string oc ")");
				(if needsForAll then output_string oc ")");
				output_string oc "))\n"
			end
		end
	) dg ()
;;

let askZ3ForRedundantEdges dg oc =
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	in
	DG.foldnodes (fun n () ->
		if (match n.nkind.nodeintlbl with NNAnd _ -> true | _ -> false) then
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
					output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
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
		match n0.nkind.nodeintlbl with
			| NNMaximum ->
			begin
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
						output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
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
					output_string oc "(pop)\n"
				) n0 ()
			end
			| _ -> ()
	) !currdg ()
	in
	output_string oc "(exit)\n";
	flush oc
;;

let removeRedundantMaxEdges_alternate dg0 =
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
					output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
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
				let answer = try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
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
	print_endline "Telling \"exit\" to Z3";
	output_string oc "(exit)\n";
	print_endline "Did put \"exit\" on output channel. Now flushing it";
	flush oc;
	print_endline "Flushed the channel. Let us flush all other channels as well";
	flush_all ();
	print_endline "Flushed all other channels. Let us close the Z3 process";
	ignore (Unix.close_process (ic,oc));
	print_endline "Closed the Z3 process";
	!currdg
;;

let removeRedundantEdgesWithZ3_alternate dg0 =
	print_endline "Enter removeRedundantEdges";
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	in
	let currdg = ref dg0
	and runagain = ref true
	and (ic,oc) = Unix.open_process "z3 -in"
	in
	output_string oc "(set-option :timeout 2000)\n";
	while !runagain do
		print_endline "Start iteration";
		runagain := false;
		output_string oc "(reset)\n";
		writeBooleanDescToZ3 !currdg oc None;
		print_string "Sent description to Z3\n";
		let dgForIter = !currdg
		in
		DG.foldnodes (fun n0 () ->
			if (match n0.nkind.nodeintlbl with NNAnd _ -> true | _ -> false) then
			begin
				print_endline ("Working with node no. " ^ (NewName.to_string n0.id));
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
						print_endline ("No changes yet. Working with edge no. " ^ (NewName.to_string testeid));
						let Some (previd, _, backmap) = cc.(0)
						in
						output_string oc "(push)\n";
						Array.iteri (fun idx _ ->
							output_string oc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
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
						print_endline "Calling check-sat";
						output_string oc "(check-sat)\n";
						flush oc;
						let answer = try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
						in
						print_endline "Received answer";
						(if answer = "unknown" then
						begin
							print_endline ("Could not figure out if edge " ^ (NewName.to_string testeid) ^ " is removable")
						end);
						(if answer = "unsat" then
						begin
							print_endline "The answer was UNSAT\n";
							changes := true;
							runagain := true;
							currdg := DG.remedge testeid !currdg;
							print_endline ("Getting rid of edge no. " ^ (NewName.to_string testeid));
						end);
						output_string oc "(pop)\n";
					end
				) n ()
			end
		) dgForIter ()
	done;
	print_endline "Telling \"exit\" to Z3";
	output_string oc "(exit)\n";
	print_endline "Did put \"exit\" on output channel. Now flushing it";
	flush oc;
	print_endline "Flushed the channel. Let us flush all other channels as well";
	flush_all ();
	print_endline "Flushed all other channels. Let us close the Z3 process";
	ignore (Unix.close_process (ic,oc));
	print_endline "Closed the Z3 process";
	!currdg
;;

let rrewz_entry_count = ref 0;;

let removeRedundantMaxEdges dg0 =
	print_endline "Enter removeRedundantMaxEdges";
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	and writeBothChans oc1 oc2 s = (output_string oc1 s; output_string oc2 s)
	in
	let x = !rrewz_entry_count
	in
	rrewz_entry_count := x + 1;
	let tc = open_tmpout ("removeRedundantMaxEdges_" ^ (string_of_int x))
	in
	let currdg = ref (DG.foldedges (fun ((IxM cc, eid), ntgt, prt) dgcurr ->
		let Some (srcid, _, _) = cc.(0)
		in
		let nsrc = DG.findnode srcid dgcurr
		in
		if (nsrc.nkind.nodeintlbl = NNError) && ((portdesc prt).inputnum = PortUnbounded) then
			DG.remedge eid dgcurr
		else dgcurr
	) dg0 dg0)
	and runagain = ref true
	in
	while !runagain do
		print_endline "Start iteration";
		runagain := false;
		let dgForIter = !currdg
		in
		DG.foldnodes (fun n0 () ->
			let isTimepointComparison nx =
				DG.nodefoldedges (fun ((IxM cc, _),_,_) b ->
					if (not b) then false else
					let Some (srcid,_,_) = cc.(0)
					in
					let srcn = DG.findnode srcid dgForIter
					in
					(srcn.nkind.outputtype = VTimePoint)
				) nx true
			in
			if (n0.nkind.nodeintlbl = NNMaximum) || ((n0.nkind.nodeintlbl = NNOperation OPLessThan) && (isTimepointComparison n0)) then
			begin
				print_endline ("Working with node no. " ^ (NewName.to_string n0.id));
				let changes = ref false
				and n = DG.findnode n0.id !currdg
				in
				let (AITT na) = n.inputindextype
				and (IxM ncc) = n.ixtypemap
				in
				let Some (_, _, fwdmap) = ncc.(0)
				in
				(if n0.nkind.nodeintlbl = NNMaximum then
				begin
					DG.nodefoldedges (fun ((IxM cc, testeid), _, _) () ->
					(* if not !changes then *)
						begin
							print_endline ("Working with edge no. " ^ (NewName.to_string testeid));
							output_string tc ("Working with edge no. " ^ (NewName.to_string testeid) ^ "\n");
							let answer =
							try
								let inpPipeOut, inpPipeIn = Unix.pipe ()
								and outpPipeOut, outpPipeIn = Unix.pipe ()
								and errPipeOut, errPipeIn = Unix.pipe ()
								in
								let ic = Unix.in_channel_of_descr inpPipeOut
								and oc = Unix.out_channel_of_descr outpPipeIn
								in
								set_binary_mode_in ic false;
								set_binary_mode_out oc false;
								let z3Pid = Unix.create_process "z3" [| "z3"; "-in" |] outpPipeOut inpPipeIn errPipeIn 
								in
								writeBothChans oc tc "(set-option :timeout 20)\n";
								writeBothChans oc tc "(declare-sort S)\n";
								writeOrderingToZ3 !currdg oc;
								writeOrderingToZ3 !currdg tc;
								print_string "Sent description to Z3\n";
								let Some (previd, _, backmap) = cc.(0)
								in
								Array.iteri (fun idx _ ->
									writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
								) na.(0);
								DG.nodefoldedges (fun ((IxM cc',eid'),_,_) () ->
									if testeid = eid' then () else
									let Some (previd',_,backmap') = cc'.(0)
									in
									writeBothChans oc tc "(assert (";
									writeBothChans oc tc (if testeid < eid' then "< " else "<= ");
									writeBothChans oc tc (idAndArgsToStr previd' backmap');
									writeBothChans oc tc " ";
									writeBothChans oc tc (idAndArgsToStr previd backmap);
									writeBothChans oc tc "))\n"
								) n0 ();
								print_endline "Calling check-sat";
								writeBothChans tc oc "(check-sat)\n";
								flush oc;
								let res =
									let (rdThis, _, _) = Unix.select [inpPipeOut] [] [] 0.02
									in
									if rdThis = [] then
									begin
										print_string "Not ready. "; "unknown"
									end
									else
									begin
										try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
									end
								in
								Unix.kill z3Pid 9;
								Unix.close inpPipeOut;
								Unix.close inpPipeIn;
								Unix.close outpPipeOut;
								Unix.close outpPipeIn;
								Unix.close errPipeOut;
								Unix.close errPipeIn;
								let (_,pstat) = Unix.waitpid [] z3Pid
								in
								(
									match pstat with
									| Unix.WEXITED x -> print_endline ("z3 terminated normally with exit code " ^ (string_of_int x))
									| Unix.WSIGNALED x -> print_endline ("z3 was killed with the signal " ^ (string_of_int x))
									| Unix.WSTOPPED x -> print_endline ("z3 was stopped with the signal " ^ (string_of_int x))
								);
								res
							with Unix.Unix_error (_,_,_) -> (print_string "Got UNIX error. "; "unknown")
							in
							print_endline "Received answer";
							(if answer = "unknown" then
							begin
								print_endline ("Could not figure out if max-input edge " ^ (NewName.to_string testeid) ^ " is removable")
							end);
							(if answer = "unsat" then
							begin
								print_endline "The answer was UNSAT";
								changes := true;
								runagain := true;
								currdg := DG.remedge testeid !currdg;
								print_endline ("Getting rid of edge no. " ^ (NewName.to_string testeid));
							end);
							output_string tc ("Answer is " ^ answer ^ "\n");
						end
					) n ()
				end else if n.nkind.nodeintlbl = NNOperation OPLessThan then
				begin
					let alwaysFalse = ref false
					and alwaysTrue = ref false
					in
					let answer =
					try
						let inpPipeOut, inpPipeIn = Unix.pipe ()
						and outpPipeOut, outpPipeIn = Unix.pipe ()
						and errPipeOut, errPipeIn = Unix.pipe ()
						in
						let ic = Unix.in_channel_of_descr inpPipeOut
						and oc = Unix.out_channel_of_descr outpPipeIn
						in
						set_binary_mode_in ic false;
						set_binary_mode_out oc false;
						let z3Pid = Unix.create_process "z3" [| "z3"; "-in" |] outpPipeOut inpPipeIn errPipeIn 
						in
					writeBothChans oc tc "(set-option :timeout 20)\n";
					writeBothChans oc tc "(declare-sort S)\n";
					writeOrderingToZ3 !currdg oc;
					writeOrderingToZ3 !currdg tc;
					print_string "Sent description to Z3\n";
					let eid1 = IdtSet.choose (DG.edges_to_port !currdg n0.id (PortOperInput 1))
					and eid2 = IdtSet.choose (DG.edges_to_port !currdg n0.id (PortOperInput 2))
					in
					let ((IxM cc1,_),_,_) = DG.findedge eid1 !currdg
					and ((IxM cc2,_),_,_) = DG.findedge eid2 !currdg
					in
					let Some (srcid1,_,backmap1) = cc1.(0)
					and Some (srcid2,_,backmap2) = cc2.(0)
					in
					Array.iteri (fun idx _ ->
						writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n");
					) na.(0);
					writeBothChans oc tc "(push)\n";
					writeBothChans oc tc "(assert (< ";
					writeBothChans oc tc (idAndArgsToStr srcid1 backmap1);
					writeBothChans oc tc " ";
					writeBothChans oc tc (idAndArgsToStr srcid2 backmap2);
					writeBothChans oc tc "))\n";
					print_endline "Calling check-sat for always false";
					writeBothChans oc tc "(check-sat)\n";
					flush oc;
						let res =
							let (rdThis, _, _) = Unix.select [inpPipeOut] [] [] 0.02
							in
							if rdThis = [] then
							begin
								print_string "Not ready. "; "unknown"
							end
							else
							begin
								try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
							end
						in
						Unix.kill z3Pid 9;
						Unix.close inpPipeOut;
						Unix.close inpPipeIn;
						Unix.close outpPipeOut;
						Unix.close outpPipeIn;
						Unix.close errPipeOut;
						Unix.close errPipeIn;
						let (_,pstat) = Unix.waitpid [] z3Pid
						in
						(
							match pstat with
							| Unix.WEXITED x -> print_endline ("z3 terminated normally with exit code " ^ (string_of_int x))
							| Unix.WSIGNALED x -> print_endline ("z3 was killed with the signal " ^ (string_of_int x))
							| Unix.WSTOPPED x -> print_endline ("z3 was stopped with the signal " ^ (string_of_int x))
						);
						res
					with Unix.Unix_error (_,_,_) -> (print_string "Got UNIX error. "; "unknown")
					in
					print_endline "Received answer";
					output_string tc ("Answer is " ^ answer ^ "\n");
					(if answer = "unknown" then
						print_endline "Received \"unknown\""
					);
					(if answer = "unsat" then
					begin
						print_endline "The answer was UNSAT";
						alwaysFalse := true;
					end);
					let answer =
					try
						let inpPipeOut, inpPipeIn = Unix.pipe ()
						and outpPipeOut, outpPipeIn = Unix.pipe ()
						and errPipeOut, errPipeIn = Unix.pipe ()
						in
						let ic = Unix.in_channel_of_descr inpPipeOut
						and oc = Unix.out_channel_of_descr outpPipeIn
						in
						set_binary_mode_in ic false;
						set_binary_mode_out oc false;
						let z3Pid = Unix.create_process "z3" [| "z3"; "-in" |] outpPipeOut inpPipeIn errPipeIn 
						in
					writeBothChans oc tc "(set-option :timeout 20)\n";
					writeBothChans oc tc "(declare-sort S)\n";
					writeOrderingToZ3 !currdg oc;
					writeOrderingToZ3 !currdg tc;
					print_string "Sent description to Z3\n";
					let eid1 = IdtSet.choose (DG.edges_to_port !currdg n0.id (PortOperInput 1))
					and eid2 = IdtSet.choose (DG.edges_to_port !currdg n0.id (PortOperInput 2))
					in
					let ((IxM cc1,_),_,_) = DG.findedge eid1 !currdg
					and ((IxM cc2,_),_,_) = DG.findedge eid2 !currdg
					in
					let Some (srcid1,_,backmap1) = cc1.(0)
					and Some (srcid2,_,backmap2) = cc2.(0)
					in
					Array.iteri (fun idx _ ->
						writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n");
					) na.(0);
					writeBothChans oc tc "(assert(<= ";
					writeBothChans oc tc (idAndArgsToStr srcid2 backmap2);
					writeBothChans oc tc " ";
					writeBothChans oc tc (idAndArgsToStr srcid1 backmap1);
					writeBothChans oc tc "))\n";
					print_endline "Calling check-sat for always true";
					writeBothChans oc tc "(check-sat)\n";
					flush oc;
						let res =
							let (rdThis, _, _) = Unix.select [inpPipeOut] [] [] 0.02
							in
							if rdThis = [] then
							begin
								print_string "Not ready. "; "unknown"
							end
							else
							begin
								try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
							end
						in
						Unix.kill z3Pid 9;
						Unix.close inpPipeOut;
						Unix.close inpPipeIn;
						Unix.close outpPipeOut;
						Unix.close outpPipeIn;
						Unix.close errPipeOut;
						Unix.close errPipeIn;
						let (_,pstat) = Unix.waitpid [] z3Pid
						in
						(
							match pstat with
							| Unix.WEXITED x -> print_endline ("z3 terminated normally with exit code " ^ (string_of_int x))
							| Unix.WSIGNALED x -> print_endline ("z3 was killed with the signal " ^ (string_of_int x))
							| Unix.WSTOPPED x -> print_endline ("z3 was stopped with the signal " ^ (string_of_int x))
						);
						res
					with Unix.Unix_error (_,_,_) -> (print_string "Got UNIX error. "; "unknown")
					in
					print_endline "Received answer";
					output_string tc ("Answer is " ^ answer ^ "\n");
					(if answer = "unknown" then
						print_endline "Received \"unknown\""
					);
					(if answer = "unsat" then
					begin
						print_endline "The answer was UNSAT";
						alwaysTrue := true;
					end);
					(if !alwaysFalse || !alwaysTrue then
					begin
						let nnew = {n with nkind = if !alwaysFalse then nkFalse else nkTrue; inputs = PortMap.empty}
						in
						currdg := DG.changenode nnew !currdg
					end)
				end);
			end
		) dgForIter ()
	done;
	close_out tc;
	!currdg
;;

(*
let removeRedundantEdgesWithZ3 dg0 eqDimsInformation =
	print_endline "Enter removeRedundantEdges";
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	and writeBothChans oc1 oc2 s = (output_string oc1 s; output_string oc2 s)
	and z3chanIsBad = ref false
	in
	let x = !rrewz_entry_count
	in
	rrewz_entry_count := x + 1;
	let tc = open_tmpout ("removeRedundantEdges_" ^ (string_of_int x))
	in
	let currdg = ref dg0
	and runagain = ref true
	in
	while !runagain do
		print_endline "Start iteration";
		runagain := false;
		if eqDimsInformation <> None then
		begin
			let dgForIter = !currdg
			in
			DG.foldnodes (fun n0 () ->
				if (match n0.nkind.nodeintlbl with NNAnd bb | NNOr bb | NNLongOr bb | NNLongAnd bb -> true | _ -> false) then
				begin
					print_endline ("Trying to remove node no. " ^ (NewName.to_string n0.id));
					let (AITT nb) = n0.inputindextype
					in
					let (ic,oc) = Unix.open_process "z3 -in"
					in
					writeBothChans oc tc "(set-option :timeout 20)\n";
					writeBothChans oc tc "(declare-sort S)\n";
					writeBooleanDescToZ3 !currdg oc eqDimsInformation;
					writeBooleanDescToZ3 !currdg tc eqDimsInformation;
					print_string "Sent description to Z3\n";
					Array.iteri (fun idx _ ->
						writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
					) nb.(0);
					writeBothChans tc oc "(assert ";
					writeBothChans oc tc (idAndArgsToStr n0.id (Array.init (Array.length nb.(0)) (fun i -> i)));
					writeBothChans tc oc ")\n";
					print_endline "Calling check-sat";
					writeBothChans tc oc "(check-sat)\n";
					flush oc;
					let answer = try input_line ic with End_of_file -> (print_string "Got EOF. "; z3chanIsBad := true; "unknown")
					in
					print_endline "Received answer";
					(if answer = "unknown" then
					begin
						print_endline ("Could not figure out if node " ^ (NewName.to_string n0.id) ^ " is always false")
					end);
					(if answer = "unsat" then
					begin
						print_endline "The answer was UNSAT\n";
						runagain := true;
						let newn = {
							id = n0.id;
							nkind = nkFalse;
							inputindextype = n0.outputindextype;
							outputindextype = n0.outputindextype;
							ixtypemap = identityIndexMap () n0.outputindextype;
							inputs = PortMap.empty;
						}
						in
						currdg := DG.changenode newn !currdg;
						print_endline ("Getting rid of node no. " ^ (NewName.to_string n0.id));
					end);
					print_endline "Telling \"exit\" to Z3";
					(if !z3chanIsBad then output_string tc else writeBothChans oc tc) "(exit)\n";
					output_string tc ("Answer is " ^ answer ^ "\n");
					print_endline "Did put \"exit\" on output channels. Now flushing them all";
					flush_all ();
					print_endline "Flushed all other channels. Let us close the Z3 process";
					ignore (Unix.close_process (ic,oc));
					print_endline "Closed the Z3 process";
					z3chanIsBad := false
				end
			) dgForIter ()
		end;
		let dgForIter = !currdg
		in
		DG.foldnodes (fun n0 () ->
			if (match n0.nkind.nodeintlbl with NNAnd _ | NNOr _ -> true | _ -> false) then
			begin
				print_endline ("Working with node no. " ^ (NewName.to_string n0.id));
				let changes = ref false
				and isAnd = (match n0.nkind.nodeintlbl with NNAnd _ -> true | _ -> false)
				and n = DG.findnode n0.id !currdg
				in
				let (AITT na) = n.inputindextype
				and (IxM ncc) = n.ixtypemap
				in
				let Some (_, _, fwdmap) = ncc.(0)
				in
				DG.nodefoldedges (fun ((IxM cc, testeid), _, _) () ->
					(* if not !changes then *)
					begin
						print_endline ("Working with edge no. " ^ (NewName.to_string testeid));
						output_string tc ("Working with edge no. " ^ (NewName.to_string testeid) ^ "\n");
						let (ic,oc) = Unix.open_process "z3 -in"
						in
						writeBothChans oc tc "(set-option :timeout 20)\n";
						writeBothChans oc tc "(declare-sort S)\n";
						writeBooleanDescToZ3 !currdg oc eqDimsInformation;
						writeBooleanDescToZ3 !currdg tc eqDimsInformation;
						print_string "Sent description to Z3\n";
						let Some (previd, _, backmap) = cc.(0)
						in
						Array.iteri (fun idx _ ->
							writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
						) na.(0);
						DG.nodefoldedges (fun ((IxM cc', othereid), _, _) () ->
							if othereid <> testeid then
							begin
								let Some (previd', _, backmap') = cc'.(0)
								in
								writeBothChans oc tc "(assert ";
								(if not isAnd then writeBothChans oc tc "(not ");
								writeBothChans oc tc (idAndArgsToStr previd' backmap');
								(if not isAnd then writeBothChans tc oc ")");
								writeBothChans tc oc ")\n"
							end
						) n ();
						writeBothChans tc oc "(assert ";
						(if isAnd then writeBothChans tc oc "(not ");
						writeBothChans tc oc (idAndArgsToStr previd backmap);
						(if isAnd then writeBothChans tc oc ")");
						writeBothChans tc oc ")\n";
						print_endline "Calling check-sat";
						writeBothChans tc oc "(check-sat)\n";
						flush oc;
						let answer = try input_line ic with End_of_file -> (print_string "Got EOF. "; z3chanIsBad := true; "unknown")
						in
						print_endline "Received answer";
						(if answer = "unknown" then
						begin
							print_endline ("Could not figure out if edge " ^ (NewName.to_string testeid) ^ " is removable")
						end);
						(if answer = "unsat" then
						begin
							print_endline "The answer was UNSAT\n";
							changes := true;
							runagain := true;
							currdg := DG.remedge testeid !currdg;
							print_endline ("Getting rid of edge no. " ^ (NewName.to_string testeid));
						end);
						print_endline "Telling \"exit\" to Z3";
						(if !z3chanIsBad then output_string tc else writeBothChans oc tc) "(exit)\n";
						output_string tc ("Answer is " ^ answer ^ "\n");
						print_endline "Did put \"exit\" on output channels. Now flushing them all";
						flush_all ();
						print_endline "Flushed all other channels. Let us close the Z3 process";
						ignore (Unix.close_process (ic,oc));
						print_endline "Closed the Z3 process";
						z3chanIsBad := false
					end
				) n ()
			end
		) dgForIter ()
	done;
	close_out tc;
	!currdg
;;
*)

let removeRedundantEdgesWithZ3 dg0 eqDimsInformation =
	print_endline "Enter removeRedundantEdges";
	let idAndArgsToStr = idAndArgsToStrWithPref "d"
	and writeBothChans oc1 oc2 s = (output_string oc1 s; output_string oc2 s)
	and z3chanIsBad = ref false
	in
	let x = !rrewz_entry_count
	in
	rrewz_entry_count := x + 1;
	let tc = open_tmpout ("removeRedundantEdges_" ^ (string_of_int x))
	in
	let currdg = ref dg0
	and runagain = ref true
	in
	while !runagain do
		print_endline "Start iteration";
		runagain := false;
		if eqDimsInformation <> None then
		begin
			let dgForIter = !currdg
			in
			DG.foldnodes (fun n0 () ->
				if (match n0.nkind.nodeintlbl with NNAnd bb | NNOr bb | NNLongOr bb | NNLongAnd bb -> true | _ -> false) then
				begin
					print_endline ("Trying to remove node no. " ^ (NewName.to_string n0.id));
					let (AITT nb) = n0.inputindextype
					in
					let answer =
					try
					let inpPipeOut, inpPipeIn = Unix.pipe ()
					and outpPipeOut, outpPipeIn = Unix.pipe ()
					and errPipeOut, errPipeIn = Unix.pipe ()
					in
					let ic = Unix.in_channel_of_descr inpPipeOut
					and oc = Unix.out_channel_of_descr outpPipeIn
					in
					set_binary_mode_in ic false;
					set_binary_mode_out oc false;
					let z3Pid = Unix.create_process "z3" [| "z3"; "-in" |] outpPipeOut inpPipeIn errPipeIn 
					in
					writeBothChans oc tc "(set-option :timeout 18)\n";
					writeBothChans oc tc "(declare-sort S)\n";
					writeBooleanDescToZ3 !currdg oc eqDimsInformation;
					writeBooleanDescToZ3 !currdg tc eqDimsInformation;
					print_string "Sent description to Z3\n";
					Array.iteri (fun idx _ ->
						writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
					) nb.(0);
					writeBothChans tc oc "(assert ";
					writeBothChans oc tc (idAndArgsToStr n0.id (Array.init (Array.length nb.(0)) (fun i -> i)));
					writeBothChans tc oc ")\n";
					print_endline "Calling check-sat";
					writeBothChans tc oc "(check-sat)\n";
					flush oc;
					let res =
						let (rdThis, _, _) = Unix.select [inpPipeOut] [] [] 0.02
						in
						if rdThis = [] then
						begin
							print_string "Not ready. "; "unknown"
						end
						else
						begin
							try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
						end
					in
					Unix.kill z3Pid 9;
					Unix.close inpPipeOut;
					Unix.close inpPipeIn;
					Unix.close outpPipeOut;
					Unix.close outpPipeIn;
					Unix.close errPipeOut;
					Unix.close errPipeIn;
					let (_,pstat) = Unix.waitpid [] z3Pid
					in
					(
						match pstat with
						| Unix.WEXITED x -> print_endline ("z3 terminated normally with exit code " ^ (string_of_int x))
						| Unix.WSIGNALED x -> print_endline ("z3 was killed with the signal " ^ (string_of_int x))
						| Unix.WSTOPPED x -> print_endline ("z3 was stopped with the signal " ^ (string_of_int x))
					);
					res
					with Unix.Unix_error (_,_,_) -> (print_string "Got UNIX error. "; "unknown")
					in
					print_endline "Received answer";
					(if answer = "unknown" then
					begin
						print_endline ("Could not figure out if node " ^ (NewName.to_string n0.id) ^ " is always false")
					end);
					(if answer = "unsat" then
					begin
						print_endline "The answer was UNSAT\n";
						runagain := true;
						let newn = {
							id = n0.id;
							nkind = nkFalse;
							inputindextype = n0.outputindextype;
							outputindextype = n0.outputindextype;
							ixtypemap = identityIndexMap () n0.outputindextype;
							inputs = PortMap.empty;
						}
						in
						currdg := DG.changenode newn !currdg;
						print_endline ("Getting rid of node no. " ^ (NewName.to_string n0.id));
					end)
				end
			) dgForIter ()
		end;
		let dgForIter = !currdg
		in
		DG.foldnodes (fun n0 () ->
			if (match n0.nkind.nodeintlbl with NNAnd _ | NNOr _ -> true | _ -> false) then
			begin
				print_endline ("Working with node no. " ^ (NewName.to_string n0.id));
				let changes = ref false
				and isAnd = (match n0.nkind.nodeintlbl with NNAnd _ -> true | _ -> false)
				and n = DG.findnode n0.id !currdg
				in
				let (AITT na) = n.inputindextype
				and (IxM ncc) = n.ixtypemap
				in
				let Some (_, _, fwdmap) = ncc.(0)
				in
				DG.nodefoldedges (fun ((IxM cc, testeid), _, _) () ->
					(* if not !changes then *)
					begin
						print_endline ("Working with edge no. " ^ (NewName.to_string testeid));
						output_string tc ("Working with edge no. " ^ (NewName.to_string testeid) ^ "\n");
						let answer =
						try
						let inpPipeOut, inpPipeIn = Unix.pipe ()
						and outpPipeOut, outpPipeIn = Unix.pipe ()
						and errPipeOut, errPipeIn = Unix.pipe ()
						in
						let ic = Unix.in_channel_of_descr inpPipeOut
						and oc = Unix.out_channel_of_descr outpPipeIn
						in
						set_binary_mode_in ic false;
						set_binary_mode_out oc false;
						let z3Pid = Unix.create_process "z3" [| "z3"; "-in" |] outpPipeOut inpPipeIn errPipeIn 
						in
						writeBothChans oc tc "(set-option :timeout 18)\n";
						writeBothChans oc tc "(declare-sort S)\n";
						writeBooleanDescToZ3 !currdg oc eqDimsInformation;
						writeBooleanDescToZ3 !currdg tc eqDimsInformation;
						print_string "Sent description to Z3\n";
						let Some (previd, _, backmap) = cc.(0)
						in
						Array.iteri (fun idx _ ->
							writeBothChans oc tc ("(declare-fun d" ^ (string_of_int idx) ^ " () S)\n")
						) na.(0);
						DG.nodefoldedges (fun ((IxM cc', othereid), _, _) () ->
							if othereid <> testeid then
							begin
								let Some (previd', _, backmap') = cc'.(0)
								in
								writeBothChans oc tc "(assert ";
								(if not isAnd then writeBothChans oc tc "(not ");
								writeBothChans oc tc (idAndArgsToStr previd' backmap');
								(if not isAnd then writeBothChans tc oc ")");
								writeBothChans tc oc ")\n"
							end
						) n ();
						writeBothChans tc oc "(assert ";
						(if isAnd then writeBothChans tc oc "(not ");
						writeBothChans tc oc (idAndArgsToStr previd backmap);
						(if isAnd then writeBothChans tc oc ")");
						writeBothChans tc oc ")\n";
						print_endline "Calling check-sat";
						writeBothChans tc oc "(check-sat)\n";
						flush oc;
						let (rdThis, _, _) = Unix.select [inpPipeOut] [] [] 0.02
						in
						let res =
							if rdThis = [] then
							begin
								print_string "Not ready. "; "unknown"
							end
							else
							begin
								try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
							end
						in
						Unix.kill z3Pid 9;
						Unix.close inpPipeOut;
						Unix.close inpPipeIn;
						Unix.close outpPipeOut;
						Unix.close outpPipeIn;
						Unix.close errPipeOut;
						Unix.close errPipeIn;
						let (_,pstat) = Unix.waitpid [] z3Pid
						in
						(
							match pstat with
							| Unix.WEXITED x -> print_endline ("z3 terminated normally with exit code " ^ (string_of_int x))
							| Unix.WSIGNALED x -> print_endline ("z3 was killed with the signal " ^ (string_of_int x))
							| Unix.WSTOPPED x -> print_endline ("z3 was stopped with the signal " ^ (string_of_int x))
						);
						res
						with Unix.Unix_error (_,_,_) -> (print_string "Got UNIX error. "; "unknown")
						in
						print_endline "Received answer";
						(if answer = "unknown" then
						begin
							print_endline ("Could not figure out if edge " ^ (NewName.to_string testeid) ^ " is removable")
						end);
						(if answer = "unsat" then
						begin
							print_endline "The answer was UNSAT\n";
							changes := true;
							runagain := true;
							currdg := DG.remedge testeid !currdg;
							print_endline ("Getting rid of edge no. " ^ (NewName.to_string testeid));
						end)
					end
				) n ()
			end
		) dgForIter ()
	done;
	close_out tc;
	!currdg
;;


let answerReachabilityQuestion dg (possIc,oc) srcids tgtids flowThroughs checks =
	print_string "Q: ";
	let print_idtset ids = print_string (String.concat ", " (List.map NewName.to_string (IdtSet.elements ids)))
	in
	print_string "src: ";
	print_idtset srcids;
	print_string " tgt: ";
	print_idtset tgtids;
	print_string " flows: ";
	print_idtset flowThroughs;
	print_string " chks: ";
	print_idtset checks;
	print_newline ();
	let mkForall oitype pref nid =
		if (Array.length oitype) = 0 then ((fun () -> ()), (fun () -> ()), fun () -> output_string oc pref; output_string oc (NewName.to_string nid))
		else
		let nbinps = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "(x" ^ (string_of_int idx) ^ " S)") oitype))
		and nbvars = String.concat " " (Array.to_list (Array.mapi (fun idx _ -> "x" ^ (string_of_int idx)) oitype))
		in
		let f1 () = output_string oc ("(forall (" ^ nbinps ^ ") ")
		and f2 () = output_string oc ")"
		and f3 () = output_string oc "("; output_string oc pref; output_string oc (NewName.to_string nid); output_string oc " "; output_string oc nbvars; output_string oc ")"
		in (f1,f2,f3)
	and vIdAndArgsToStr = selIdAndArgsToStrWithPref "v" "x"
	and fIdAndArgsToStr = selIdAndArgsToStrWithPref "f" "x"
	in
	output_string oc "(push)\n";
	IdtSet.iter (fun flowNodeId ->
		let n = DG.findnode flowNodeId dg
		in
		let (AITT nb) = n.outputindextype
		in
		let (forall_open, forall_close, outf) = mkForall nb.(0) "f" n.id
		in
		output_string oc "(assert ";
		forall_open ();
		output_string oc "(not ";
		outf ();
		forall_close ();
		output_string oc "))\n"
	) flowThroughs;
	DG.foldnodes (fun n () ->
		if IdtSet.mem n.id srcids then () else
		match n.nkind.nodeintlbl with
			| NNInput _
			| NNInputExists _ -> begin
				let (AITT nb) = n.outputindextype
				in
				let (forall_open, forall_close, outf) = mkForall nb.(0) "f" n.id
				in
				output_string oc "(assert ";
				forall_open ();
				output_string oc "(not ";
				outf ();
				forall_close ();
				output_string oc "))\n"
			end
			| _ -> ()
	) dg ();
	IdtSet.iter (fun checkNodeId ->
		let n = DG.findnode checkNodeId dg
		in
		let (AITT nb) = n.outputindextype
		in
		let (forall_open, forall_close, outf) = mkForall nb.(0) "v" n.id
		in
		output_string oc "(assert ";
		forall_open ();
		output_string oc "(not ";
		outf ();
		forall_close ();
		output_string oc "))\n"
	) checks;
	IdtSet.iter (fun tgtNodeId ->
		let n = DG.findnode tgtNodeId dg
		in
		let (AITT nb) = n.outputindextype
		in
		Array.iteri (fun idx _ ->
			output_string oc ("(declare-fun d" ^ (NewName.to_string tgtNodeId) ^ "_" ^ (string_of_int idx) ^ " () S)\n")
		) nb.(0)
	) tgtids;
	output_string oc "(assert ";
	(if (IdtSet.cardinal tgtids) > 1 then output_string oc "(or ");
	IdtSet.iter (fun tgtNodeId ->
		let n = DG.findnode tgtNodeId dg
		in
		let (AITT nb) = n.outputindextype
		in
		(if (Array.length nb.(0)) > 0 then output_string oc "(");
		output_string oc ("f" ^ (NewName.to_string tgtNodeId));
		Array.iteri (fun idx _ ->
			output_string oc (" d" ^ (NewName.to_string tgtNodeId) ^ "_" ^ (string_of_int idx))
		) nb.(0);
		(if (Array.length nb.(0)) > 0 then output_string oc ")");
	) tgtids;
	(if (IdtSet.cardinal tgtids) > 1 then output_string oc ")");
	output_string oc ")\n";
	output_string oc "(check-sat)\n";
	flush oc;
	output_string oc "(pop)\n";
	match possIc with
		| Some ic -> (
			let answer = try input_line ic with End_of_file -> (print_string "Got EOF. "; "unknown")
			in
			(if answer = "unknown" then
			begin
				print_endline ("Received an \"unknown\"")
			end else
			begin
				print_endline ("Answer is \"" ^ answer ^ "\"")
			end);
			answer = "unsat"
		)
		| None -> false
;;

module GraphForInverseTopolSort =
struct
	type t = DG.t
	
	module V =
	struct
		type t = NewName.idtype
		
		let compare = Pervasives.compare
		let hash = Hashtbl.hash
		let equal id1 id2 = (id1 = id2)
	end
	
	let iter_vertex f dg = DG.foldnodes (fun n () -> f n.id) dg ()
	
	let iter_succ f dg nid = ignore (DG.nodefoldedges (fun ((IxM [| Some (srcid,_,_) |],_),_,_) s -> if IdtSet.mem srcid s then s else (f srcid; IdtSet.add srcid s)) (DG.findnode nid dg) IdtSet.empty); ()
	
end;;

module InverseTopolSorter = Graph.Topological.Make(GraphForInverseTopolSort);;

let findEncryptionKeySources dg =
	let currRes = ref IdtMap.empty
	in
	let processNode nid =
		let n = DG.findnode nid dg
		in
		let directKey = DG.nodefoldoutedges dg (fun ((_,_), tgtn, prt) currDK ->
			if (tgtn.nkind.nodeintlbl = NNOperation OPEncrypt) && (prt = PortOperInput 2) then IdtSet.add tgtn.id currDK else currDK
		) n IdtSet.empty
		in
		let mapsToEncs = DG.nodefoldoutedges dg (fun ((_,_),tgtn,_) currMTE ->
			IdtSet.union currMTE (IdtMap.find tgtn.id !currRes)
		) n directKey
		in
		currRes := IdtMap.add nid mapsToEncs !currRes
	in
	InverseTopolSorter.iter processNode dg;
	IdtMap.filter (fun k _ -> let n = DG.findnode k dg in match n.nkind.nodeintlbl with NNInput _ -> true | _ -> false) !currRes
;;

let addEncryptionAnalysisNodes dg =
	(* create extra output nodes for encryption keys *)
	DG.foldnodes (fun n dgcurr ->
		match n.nkind.nodeintlbl with
		| NNOperation OPEncrypt 
		| NNOperation (OPABEncrypt _) ->
			let keyedgeid = IdtSet.choose (DG.edges_to_port dgcurr n.id (PortOperInput 2))
			in
			let ((IxM [| Some (keynodeid, _, keybackmap) |],_),_,_) = DG.findedge keyedgeid dgcurr
			in
			let keynode = DG.findnode keynodeid dg
			in
			let outpnode = {
				nkind = nkOutput keynode.nkind.outputtype (RLSet.singleton ("Key of encryption " ^ (NewName.to_string n.id)));
				id = NewName.get ();
				inputs = PortMap.empty;
				inputindextype = keynode.outputindextype;
				outputindextype = keynode.outputindextype;
				ixtypemap = identityIndexMap () keynode.outputindextype;
			}
			and truenode = {
				nkind = nkTrue;
				id = NewName.get ();
				inputs = PortMap.empty;
				inputindextype = keynode.outputindextype;
				outputindextype = keynode.outputindextype;
				ixtypemap = identityIndexMap () keynode.outputindextype;
			}
			in
			DG.addedge (((identityIndexMap keynode.id keynode.outputindextype), NewName.get ()), outpnode.id, PortSingle keynode.nkind.outputtype) (DG.addedge (((identityIndexMap truenode.id keynode.outputindextype), NewName.get ()), outpnode.id, PortSingleB true) (DG.addnode outpnode (DG.addnode truenode dgcurr)))
		| _ -> dgcurr
	) dg dg
;;

let checkFlows dg possFName =
	let onlyMinimalResults allResults =
		let isMinimal (badFun,badCheck) = not (List.exists (fun (lFun,lCheck) -> ((lFun <> badFun) || (lCheck <> badCheck)) && (IdtSet.subset lFun badFun) && (IdtSet.subset lCheck badCheck)) allResults)
		in
		List.filter isMinimal allResults
	in
	let (ic,oc) = match possFName with
		| Some fname -> let occ = open_tmpout fname in (None, occ)
		| None -> let (icc,occ) = Unix.open_process "z3 -in" in (Some icc, occ)
	in
(*	let oc = open_tmpout "descAll.z3"
	in *)
	output_string oc "(set-option :timeout 2000)\n";
	writeItAllToZ3 dg oc;
	let allInputNodes = DG.foldnodes (fun n ss ->
		match n.nkind.nodeintlbl with
			| NNInput _ -> IdtSet.add n.id ss
			| _ -> ss
	) dg IdtSet.empty
	and allOutputNodes = DG.foldnodes (fun n ss ->
		match n.nkind.nodeintlbl with
			| NNOutput _ -> IdtSet.add n.id ss
			| _ -> ss
	) dg IdtSet.empty
	and allCheckNodes = DG.foldnodes (fun n ss ->
		let d = n.nkind.nodelabel
		in
		if ((String.length d) >= 3) && ((String.sub d 0 3) = "is_") then IdtSet.add n.id ss else ss
	) dg IdtSet.empty
	and allFilterNodes = DG.foldnodes (fun n ss ->
		if n.nkind.nodeintlbl = NNOperation OPEncrypt then IdtSet.add n.id ss else
		if (match n.nkind.nodeintlbl with NNOperation (OPABEncrypt _ ) -> true | _ -> false) then IdtSet.add n.id ss else
		let d = n.nkind.nodelabel
		in
		if ((String.length d) >= 7) && ((String.sub d 0 7) = "filter_") then IdtSet.add n.id ss else 
		if ((String.length d) >= 4) && ((String.sub d 0 4) = "hash") then IdtSet.add n.id ss else ss
	) dg IdtSet.empty
	in
	let outputNames = IdtSet.fold (fun nid mm ->
		let n = DG.findnode nid dg
		in
		let rls = (match n.nkind.nodeintlbl with NNOutput c -> c | _ -> RLSet.empty)
		in
		RLSet.fold (fun s mmm ->
			let sids = try RLMap.find s mmm with Not_found -> IdtSet.empty
			in
			let sids' = IdtSet.add nid sids
			in
			RLMap.add s sids' mmm
		) rls mm
	) allOutputNodes RLMap.empty
	in
	let answers = IdtSet.fold (fun inpNodeId m1 ->
		let answersForInpNode = RLMap.fold (fun outpName outpIds m2 ->
			(* TODO: https://en.wikipedia.org/wiki/Group_testing is related to the thing we are trying to do below. We are trying to learn a monotone boolean function. Its atoms are not necessarily singleton sets, though *)
			(* See e.g. Boris Kovalerchuk, Evangelos Triantaphyllou, Aniruddha S. Deshpande, Evgenii Vityaev. Interactive Learning of Monotone Boolean Functions. Information Sciences 94, pp. 87-118, 1996 *)
			if (* (IdtSet.is_empty allFilterNodes) && *) (IdtSet.is_empty allCheckNodes) then
			begin
				let allResults = ref []
				and withAll = ref false
				and withNone = ref false
				and string_of_idtset s = "{" ^ (String.concat ", " (List.map NewName.to_string (IdtSet.elements s))) ^ "}"
				in
				IdtSet.subsetiter (fun someFilters ->
					print_string ("FlowCheck: input: " ^ (NewName.to_string inpNodeId) ^ ", outputs: " ^ (string_of_idtset outpIds) ^ ", filters: " ^ (string_of_idtset someFilters) ^ ", result: ");
					let dg' = DG.foldnodes (fun n dgcurr ->
						match n.nkind.nodeintlbl with
						| NNOutput _ -> if IdtSet.mem n.id outpIds then dgcurr else DG.remnode n.id dgcurr
						| _ -> if IdtSet.mem n.id someFilters then dgcurr else if IdtSet.mem n.id allFilterNodes then DG.remnode n.id dgcurr else dgcurr
					) dg dg
					in
					let dg'' = GrbOptimize.removeDead dg'
					in
					let res = not (DG.hasnode inpNodeId dg'')
					in
					if res then
					begin
						(if IdtSet.is_empty someFilters then withAll := true);
						(if IdtSet.equal someFilters allFilterNodes then withNone := true);
						print_endline "true"
					end else (allResults := (someFilters, IdtSet.empty) :: !allResults; print_endline "false")
				) allFilterNodes;
				RLMap.add outpName (!withAll, !withNone, onlyMinimalResults !allResults) m2
			end
			else
			begin
				let allResults = ref [] (* allResults :: (IdtSet.t * IdtSet.t) list; contains all pairs of sets for which the reachability question answer is true *)
				and withAll = ref false
				and withNone = ref false
				in
				IdtSet.subsetiter (fun someFilters ->
					IdtSet.subsetiter (fun someChecks ->
						if answerReachabilityQuestion dg (ic,oc) (IdtSet.singleton inpNodeId) outpIds (IdtSet.diff allFilterNodes someFilters) (IdtSet.diff allCheckNodes someChecks) then begin
							(if (IdtSet.is_empty someFilters) && (IdtSet.is_empty someChecks) then withAll := true);
							(if (IdtSet.equal someFilters allFilterNodes) && (IdtSet.equal someChecks allCheckNodes) then withNone := true)
						end else allResults := (someFilters, someChecks) :: !allResults
					) allCheckNodes
				) allFilterNodes;
				RLMap.add outpName (!withAll, !withNone, onlyMinimalResults !allResults) m2
			end
		) outputNames RLMap.empty
		in
		IdtMap.add inpNodeId answersForInpNode m1
	) allInputNodes IdtMap.empty
	in
	output_string oc "(exit)\n";
	flush oc;
	(match ic with
		| Some icc -> ignore (Unix.close_process (icc,oc))
		| None -> close_out oc
	);
(*	close_out oc; *)
	answers
;;

