open GrbGraphs;;
open GrbCommons;;

let dimmapToStrWithPref vpref bm = String.concat " " (Array.to_list (Array.map (fun idx -> vpref ^ (string_of_int idx)) bm));;

let selIdAndArgsToStrWithPref npref vpref nid bm = if Array.length bm > 0 then "(" ^ npref ^ (NewName.to_string nid) ^ " " ^ (dimmapToStrWithPref vpref bm) ^ ")" else npref ^ (NewName.to_string nid);;

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
						if bb then true else if prt = PortSingleB then false else
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
	output_string oc "(declare-sort S)
(declare-fun sord (S S) Bool)
(assert (forall ((x S) (y S)) (or (sord x y) (= x y) (sord y x))))
(assert (forall ((x S)) (not (sord x x))))
(assert (forall ((x S) (y S)) (=> (sord x y) (not (sord y x)))))
(assert (forall ((x S) (y S) (z S)) (=> (and (sord x y) (sord y z)) (sord x z))))\n";
	DG.foldnodes (fun n () ->
		let (AITT nb) = n.outputindextype
		in
		let nbinps = String.concat " " (Array.to_list (Array.map (fun _ -> "S") nb.(0)))
		in
		let vType = if IdtSet.mem n.id dimProducers then "S" else if n.nkind.outputtype = VBoolean then "Bool" else "Int"
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
		for i = 1 to inpnum do
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
	) addrgens;
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
					if prt = PortSingleB then
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
		| NNAnd
		| NNOr -> begin
			output_string oc "(assert ";
			output_forall_open ();
			output_string oc "(= (";
			output_string oc (match n.nkind.nodeintlbl with | NNAnd -> "and " | _ -> "or ");
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
			output_forall_open ();
			output_string oc "(=> ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_string oc " ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc ")))\n";
			output_string oc "(assert ";
			output_string oc ("(forall (" ^ qvarsNA ^ ") ");
			output_string oc "(=> (not ";
			output_string oc (vIdAndArgsToStr n.id fwdmap);
			output_string oc ") (not ";
			output_string oc (vIdAndArgsToStr previd backmap);
			output_forall_close ();
			output_string oc ")))\n";
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
				if prt = PortSingleB then () else
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
		| NNOperation c when (match c with OPLessThan | OPGreaterThan | OPLessEqual | OPGreaterEqual | OPIsEq -> true | _ -> false) -> begin
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
(*		| NNIsEq -> begin
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
				if prt = PortSingleB then
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

let answerReachabilityQuestion dg (possIc,oc) srcids tgtids flowThroughs checks =
	let mkForall oitype pref nid =
		if (Array.length oitype) = 0 then ((fun () -> ()), (fun () -> ()), fun () -> output_string oc "pref"; output_string oc (NewName.to_string nid))
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
			let answer = input_line ic
			in
			if answer = "unknown" then
			begin
				print_endline ("Received an \"unknown\"")
			end;
			answer = "unsat"
		)
		| None -> false
;;

let checkFlows dg possFName =
	let (ic,oc) = match possFName with
		| Some fname -> let occ = open_out fname in (None, occ)
		| None -> let (icc,occ) = Unix.open_process "z3 -in" in (Some icc, occ)
	in
(*	let oc = open_out "descAll.z3"
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
		let d = n.nkind.nodelabel n.ixtypemap
		in
		if ((String.length d) >= 3) && ((String.sub d 0 3) = "is_") then IdtSet.add n.id ss else ss
	) dg IdtSet.empty
	and allFilterNodes = DG.foldnodes (fun n ss ->
		let d = n.nkind.nodelabel n.ixtypemap
		in
		if ((String.length d) >= 7) && ((String.sub d 0 7) = "filter_") then IdtSet.add n.id ss else ss
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
			let withAll = answerReachabilityQuestion dg (ic,oc) (IdtSet.singleton inpNodeId) outpIds allFilterNodes allCheckNodes
			in
			let withNone = answerReachabilityQuestion dg (ic,oc) (IdtSet.singleton inpNodeId) outpIds IdtSet.empty IdtSet.empty
			in
			let withOneFilter = IdtSet.fold (fun filterNodeId mm ->
				IdtMap.add filterNodeId (answerReachabilityQuestion dg (ic,oc) (IdtSet.singleton inpNodeId) outpIds (IdtSet.remove filterNodeId allFilterNodes) allCheckNodes) mm
			) allFilterNodes IdtMap.empty
			in
			let withOneCheck = IdtSet.fold (fun checkNodeId mm ->
				IdtMap.add checkNodeId (answerReachabilityQuestion dg (ic,oc) (IdtSet.singleton inpNodeId) outpIds allFilterNodes (IdtSet.remove checkNodeId allCheckNodes)) mm
			) allCheckNodes IdtMap.empty
			in
			RLMap.add outpName (withAll, withNone, withOneFilter, withOneCheck) m2
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

