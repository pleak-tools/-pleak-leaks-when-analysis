open GrbGraphs;;
open GrbCommons;;

type mappingDirection = MDForward | MDBackward;;

let printgraph oc dg = (* Sends the description of dg in the dot format to the channel oc *)
	let needsValuetype =
		DG.foldnodes (fun n b ->
			if b then true else
			let checkIndexType (AITT a) =
				let res = ref false
				in
				Array.iter (Array.iter (fun (vt,_) -> if vt <> VInteger then res := true)) a;
				!res
			in (checkIndexType n.inputindextype) || (checkIndexType n.outputindextype)
		) dg false
	in
	let dotnodeid x = "v_" ^ (NewName.to_string x)
	and dotedgeid x = "e_" ^ (NewName.to_string x)
	and outputMasked s =
		String.iter (function
			| '<' -> output_string oc "\\<"
			| '>' -> output_string oc "\\>"
			| c -> output_char oc c
		) s
	in
	let outputMapInVContext a b m mapdir =
		let outputSeqInVContext nums dims =
			Array.iteri (fun idx n ->
				(if idx > 0 then output_string oc "| " else ());
				let (vt,tp) = dims.(idx)
				in
				output_string oc ("{ " ^ (string_of_int n) ^ (if needsValuetype then " | " ^ (string_of_valuetype vt) else "") ^ " | ");
				(match tp with
					| None -> ()
					| Some s -> outputMasked (s ^ " ")
				);
				output_string oc "} "
			) nums
		in
		let aa = a.(0)
		and bb = b.(0)
		and mm = let Some (_,_,x) = m.(0) in x
		in
		let aseq,bseq = match mapdir with
			| MDForward -> Array.of_list (intfromto 0 ((Array.length aa) - 1)), mm
			| MDBackward -> mm, Array.of_list (intfromto 0 ((Array.length bb) - 1))
		in
		if (aa = bb) && (aseq = bseq) then
		begin
			outputSeqInVContext aseq aa
		end else
		begin
		output_string oc "{ { ";
		outputSeqInVContext aseq aa;
		output_string oc "} ";
		(match mapdir with
			| MDForward -> output_string oc " | -\\> | "
			| MDBackward -> output_string oc " | \\<- | " );
		output_string oc "{ ";
		outputSeqInVContext bseq bb;
		output_string oc "} } "
		end
	in
	output_string oc "digraph {\n";
	DG.foldnodes (fun nn () ->
		let (AITT a) = nn.inputindextype
		and (AITT b) = nn.outputindextype
		and (IxM m) = nn.ixtypemap
		in
		if (Array.length a = 1) && (Array.length b = 1) then
		begin
			output_string oc ((dotnodeid nn.id) ^ "[shape=record label=\"{ ");
			output_string oc "{ ";
			outputMasked (nn.nkind.nodelabel nn.ixtypemap);
			output_string oc (" | " ^ (NewName.to_string nn.id) ^ " } | ");
			outputMapInVContext a b m MDForward;
			output_string oc " }\"];\n"
		end else
		begin
			output_string oc ((dotnodeid nn.id) ^ " [label=\"");
			output_string oc ((nn.nkind.nodelabel nn.ixtypemap) ^ " " ^ (NewName.to_string nn.id) ^ "\"];\n")
		end
	) dg ();
	DG.foldedges (fun ((cc,eid),nn,prt) () ->
		let (IxM m) = cc
		in
		let isNonIdentity (Some (_,_,backmap)) =
			let res = ref false
			in
			Array.iteri (fun idx n -> if idx <> n then res := true) backmap;
			!res
		in
		let wiredesc = (portdesc prt).wirename ^ "\\{" ^ (NewName.to_string eid) ^ "\\}"
		in
		if (Array.length m = 1) && (match m.(0) with None -> false | Some _ -> true) && (isNonIdentity m.(0)) then
		begin
			let (AITT b) = nn.inputindextype
			in
			let Some (srcid,_,_) = m.(0)
			in
			let srcn = DG.findnode srcid dg
			in
			let (AITT a) = srcn.outputindextype
			in
			output_string oc ((dotedgeid eid) ^ "[shape=Mrecord label=\"{ " ^ wiredesc ^ " | ");
			outputMapInVContext a b m MDBackward;
			output_string oc " }\"];\n"
		end else
		begin
			output_string oc ((dotedgeid eid) ^ " [shape=plaintext label=\"" ^ wiredesc ^ "\" width=0 height=0];\n")
		end;
		DG.foldedgesources (fun srcid () ->
			output_string oc ( (dotnodeid srcid) ^ ":s -> " ^ (dotedgeid eid) ^ ":n [dir=none];\n" )
		) (cc,eid) ();
		output_string oc ( (dotedgeid eid) ^ ":s -> " ^ (dotnodeid nn.id) ^ ":n;\n" )
	) dg ();
	output_string oc "}\n";;

