open BpmnInput;;
open GrbCommons;;
open GrbGraphs;;

type nodeonpicturekind = NOPTask | NOPDataset | NOPSubprocess | NOPPool | NOPGateway | NOPEvent | NOPComment;;

type nodeonpicturetype = {
	id : NewName.idtype;
	kind : nodeonpicturekind;
	attrs : string RLMap.t;
};;

type edgeonpicturekind = EOPSeqFlow | EOPMsgFlow | EOPRead | EOPWrite | EOPContain | EOPBoundary | EOPComment;;

type edgeonpicturetype = {
	id : NewName.idtype;
	src : NewName.idtype;
	tgt : NewName.idtype;
	kind : edgeonpicturekind;
	attrs : string RLMap.t;
};;

type graphgraphtype = {
	nodes : (nodeonpicturetype * IdtSet.t * IdtSet.t) IdtMap.t;
	edges : edgeonpicturetype IdtMap.t;
};;

let grreprRemoveEdge grrepr edgeid =
	let edge = IdtMap.find edgeid grrepr.edges
	in
	let (srcn, srcout, srcin) = IdtMap.find edge.src grrepr.nodes
	and (tgtn, tgtout, tgtin) = IdtMap.find edge.tgt grrepr.nodes
	in
	{ nodes = IdtMap.add edge.src (srcn, IdtSet.remove edgeid srcout, srcin) (IdtMap.add edge.tgt (tgtn, tgtout, IdtSet.remove edgeid tgtin) grrepr.nodes);
	  edges = IdtMap.remove edgeid grrepr.edges;
	}
;;

let grreprRemoveNode grrepr nodeid =
	let (noden, nodeout, nodein) = IdtMap.find nodeid grrepr.nodes
	in
	let grmid = IdtSet.fold (fun outedgeid currgrrepr ->
		let outedge = IdtMap.find outedgeid currgrrepr.edges
		in
		let (outn, outout, outin) = IdtMap.find outedge.tgt currgrrepr.nodes
		in {
			nodes = IdtMap.add outedge.tgt (outn, outout, IdtSet.remove outedgeid outin) currgrrepr.nodes;
			edges = IdtMap.remove outedgeid currgrrepr.edges;
		}
	) nodeout (IdtSet.fold (fun inedgeid currgrrepr ->
		let inedge = IdtMap.find inedgeid currgrrepr.edges
		in
		let (inn, inout, inin) = IdtMap.find inedge.src currgrrepr.nodes
		in {
			nodes = IdtMap.add inedge.src (inn, IdtSet.remove inedgeid inout, inin) currgrrepr.nodes;
			edges = IdtMap.remove inedgeid currgrrepr.edges;
		}
	) nodein grrepr)
	in
	{grmid with nodes = IdtMap.remove nodeid grmid.nodes}
;;

let grreprMoveEdgeSource grrepr edgeid newsrcid =
	let edge = IdtMap.find edgeid grrepr.edges
	in
	if newsrcid = edge.src then grrepr else
	let (srcn, srcouts, srcins) = IdtMap.find edge.src grrepr.nodes
	and (nsrcn, nsrcouts, nsrcins) = IdtMap.find newsrcid grrepr.nodes
	in
	let msrc = (srcn, IdtSet.remove edgeid srcouts, srcins)
	and mnsrc = (nsrcn, IdtSet.add edgeid nsrcouts, nsrcins)
	and nedge = {edge with src = newsrcid}
	in
	{nodes = IdtMap.add edge.src msrc (IdtMap.add newsrcid mnsrc grrepr.nodes); edges = IdtMap.add edgeid nedge grrepr.edges;}
;;

let grreprMoveEdgeTarget grrepr edgeid newtgtid =
	let edge = IdtMap.find edgeid grrepr.edges
	in
	if newtgtid = edge.tgt then grrepr else
	let (tgtn, tgtouts, tgtins) = IdtMap.find edge.tgt grrepr.nodes
	and (ntgtn, ntgtouts, ntgtins) = IdtMap.find newtgtid grrepr.nodes
	in
	let mtgt = (tgtn, tgtouts, IdtSet.remove edgeid tgtins)
	and mntgt = (ntgtn, ntgtouts, IdtSet.add edgeid ntgtins)
	and nedge = {edge with tgt = newtgtid}
	in
	{nodes = IdtMap.add edge.tgt mtgt (IdtMap.add newtgtid mntgt grrepr.nodes); edges = IdtMap.add edgeid nedge grrepr.edges;}
;;

let grreprAddEdge grrepr edgerec =
	let (srcn, srcoutg, srcincom) = IdtMap.find edgerec.src grrepr.nodes
	and (tgtn, tgtoutg, tgtincom) = IdtMap.find edgerec.tgt grrepr.nodes
	in
	let nsrcoutg = IdtSet.add edgerec.id srcoutg
	and ntgtincom = IdtSet.add edgerec.id tgtincom
	in
	{ 	nodes = IdtMap.add srcn.id (srcn, nsrcoutg, srcincom) (IdtMap.add tgtn.id (tgtn, tgtoutg, ntgtincom) grrepr.nodes);
		edges = IdtMap.add edgerec.id edgerec grrepr.edges;
	}
;;

let grreprAddNode grrepr (noderec : nodeonpicturetype) =
	let (outgs,incs) = try
		let (_,x,y) = IdtMap.find noderec.id grrepr.nodes
		in
		(x,y)
	with Not_found -> (IdtSet.empty, IdtSet.empty)
	in
	{ grrepr with nodes = IdtMap.add noderec.id (noderec, outgs, incs) grrepr.nodes }
;;

let grreprFindEdgesByEnds grrepr srcid tgtid =
	let (_, srcoutg, _) = IdtMap.find srcid grrepr.nodes
	and (_, _, tgtincom) = IdtMap.find tgtid grrepr.nodes
	in
	IdtSet.inter srcoutg tgtincom
;;

let areEdgesOK grrepr =
	IdtMap.iter (fun nid ((ndesc : nodeonpicturetype), nouts, nincs) ->
		IdtSet.iter (fun edgeid ->
			if IdtMap.mem edgeid grrepr.edges then
			begin
				let edge = IdtMap.find edgeid grrepr.edges
				in
				if edge.src <> nid then
					print_endline ("Edge no. " ^ (NewName.to_string edgeid) ^ " leaves node no. " ^ (NewName.to_string edge.src) ^ ", but is included among outgoing edges of node no. " ^ (NewName.to_string nid))
			end
			else
				print_endline ("Edge no. " ^ (NewName.to_string edgeid) ^ " does not exist, but leaves node no. " ^ (NewName.to_string nid))
		) nouts;
		IdtSet.iter (fun edgeid ->
			if IdtMap.mem edgeid grrepr.edges then
			begin
				let edge = IdtMap.find edgeid grrepr.edges
				in
				if edge.tgt <> nid then
					print_endline ("Edge no. " ^ (NewName.to_string edgeid) ^ " enters node no. " ^ (NewName.to_string edge.tgt) ^ ", but is included among incoming edges of node no. " ^ (NewName.to_string nid))
			end
			else
				print_endline ("Edge no. " ^ (NewName.to_string edgeid) ^ " does not exist, but enters node no. " ^ (NewName.to_string nid))
		) nincs
	) grrepr.nodes;
	IdtMap.iter (fun eid edge ->
		let (_, srcout, _) = IdtMap.find edge.src grrepr.nodes
		and (_, _, tgtin) = IdtMap.find edge.tgt grrepr.nodes
		in
		(if not (IdtSet.mem eid srcout) then
			print_endline ("Edge no. " ^ (NewName.to_string eid) ^ " from " ^ (NewName.to_string edge.src) ^ " to " ^ (NewName.to_string edge.tgt) ^ " is missing at the source's outgoing edge set") );
		(if not (IdtSet.mem eid tgtin) then
			print_endline ("Edge no. " ^ (NewName.to_string eid) ^ " from " ^ (NewName.to_string edge.src) ^ " to " ^ (NewName.to_string edge.tgt) ^ " is missing at the target's incoming edge set") );
	) grrepr.edges
;;

let grreprPutTaskToSeqFlow grrepr edgeid noderec =
	let edge = IdtMap.find edgeid grrepr.edges
	in
	if edge.kind <> EOPSeqFlow then grrepr else
	let gr1 = grreprAddNode grrepr noderec
	in
	let (srcn,_, srcincom) = IdtMap.find edge.src gr1.nodes
	in
	let Some (procid, containattrs) = IdtSet.fold (fun cedgeid res ->
		match res with
		| Some _ -> res
		| None ->
			let cedge = IdtMap.find cedgeid gr1.edges
			in
			if cedge.kind = EOPContain then Some (cedge.src, cedge.attrs) else None
	) srcincom None
	in
	let containedge = {
		id = NewName.get ();
		src = procid;
		tgt = noderec.id;
		kind = EOPContain;
		attrs = containattrs;
	}
	and src2newedge = {
		id = NewName.get ();
		src = edge.src;
		tgt = noderec.id;
		kind = EOPSeqFlow;
		attrs = edge.attrs;
	}
	in
	grreprMoveEdgeSource (grreprAddEdge (grreprAddEdge gr1 containedge) src2newedge) edgeid noderec.id
;;

let grreprIncomingEdgeOfKind grrepr nodeid eopkind =
	let (_, _, incom) = IdtMap.find nodeid grrepr.nodes
	in
	match IdtSet.fold (fun edgeid res ->
		match res with
		| Some _ -> res
		| None ->
			let cedge = IdtMap.find edgeid grrepr.edges
			in
			if cedge.kind = eopkind then Some edgeid else None
	) incom None
	with
	| None -> raise Not_found
	| Some rres -> rres
;;

let grreprOutgoingEdgeOfKind grrepr nodeid eopkind =
	let (_, outg, _) = IdtMap.find nodeid grrepr.nodes
	in
	match IdtSet.fold (fun edgeid res ->
		match res with
		| Some _ -> res
		| None ->
			let cedge = IdtMap.find edgeid grrepr.edges
			in
			if cedge.kind = eopkind then Some edgeid else None
	) outg None
	with
	| None -> raise Not_found
	| Some rres -> rres
;;

let isProcessStartNode grrepr nodeid =
	let (node, _, nins) = IdtMap.find nodeid grrepr.nodes
	in
	((node.kind = NOPEvent) || (node.kind = NOPTask) || (node.kind = NOPGateway)) &&
	(IdtSet.for_all (fun edgeid ->
		let edge = IdtMap.find edgeid grrepr.edges
		in
		edge.kind <> EOPSeqFlow
	) nins)
;;

let isProcessEndNode grrepr nodeid =
	let (node, nouts, _) = IdtMap.find nodeid grrepr.nodes
	in
	((node.kind = NOPEvent) || (node.kind = NOPTask) || (node.kind = NOPGateway)) &&
	(IdtSet.for_all (fun edgeid ->
		let edge = IdtMap.find edgeid grrepr.edges
		in
		edge.kind <> EOPSeqFlow
	) nouts)
;;

let findProcessNodesWithProperty pred grrepr procid =
	let (procn, procouts, procins) = IdtMap.find procid grrepr.nodes
	in
	IdtSet.fold (fun cntedgeid ll ->
		let cntedge = IdtMap.find cntedgeid grrepr.edges
		in
		if cntedge.kind <> EOPContain then ll else
		if pred grrepr cntedge.tgt then cntedge.tgt :: ll else ll
	) procouts []
;;

let findProcessStartNodes = findProcessNodesWithProperty isProcessStartNode;;

let findProcessEndNodes = findProcessNodesWithProperty isProcessEndNode;;

let findTopProcessNodes grrepr =
	IdtMap.fold (fun procid ((procn : nodeonpicturetype), procoutg, procincom) ss ->
		if procn.kind <> NOPSubprocess then ss else
		if IdtSet.for_all (fun incedgeid ->
			let incedge = IdtMap.find incedgeid grrepr.edges
			in
			if incedge.kind <> EOPContain then true else
			let (uppern,_,_) = IdtMap.find incedge.src grrepr.nodes
			in
			if uppern.kind = NOPSubprocess then false else true
		) procincom then IdtSet.add procid ss else ss
	) grrepr.nodes IdtSet.empty
;;

let spaceToUnderscore s =
	let t = Bytes.of_string s
	and l = String.length s
	in
	for i = 0 to (l-1) do
		if (Bytes.get t i) = ' ' then Bytes.set t i '_'
	done;
	Bytes.to_string t
;;

let xmlchild frag s =
	let perhapsres = Xml.fold (fun res child ->
		match res with
		| Some _ -> res
		| None -> (
			try
				if Xml.tag child = s then Some child else None
			with Xml.Not_element _ -> None
		)
	) None frag
	in
	match perhapsres with
	| None -> raise (Xml.No_attribute s)
	| Some x -> x
;;

let xmlchilds frag s =
	Xml.fold (fun ll child ->
		try
			if Xml.tag child = s then child :: ll else ll
		with Xml.Not_element _ -> ll
	) [] frag
;;

let getPCData xmlelem = (* Xml.pcdata (List.hd (Xml.children xmlelem)) *)
	let prelres =
		match xmlelem with
		| Xml.Element (_, _, children) -> (
			match children with
			| [] -> ""
			| xx :: _ -> Xml.pcdata xx
		)
		| Xml.PCData s -> s
	in
	let buf = Buffer.create ((String.length prelres) - 5)
	and rembuf = Buffer.create 5
	in
	for i = 0 to (String.length prelres) - 1 do
		let x = Buffer.length rembuf
		and c = prelres.[i]
		in
		if  ((x = 0) && (c = '&')) ||
			((x = 1) && (c = '#')) ||
			((x = 2) && (c = '1')) ||
			((x = 3) && (c = '0')) ||
			((x = 4) && (c = ';')) then
		begin
			if x = 4 then Buffer.clear rembuf else Buffer.add_char rembuf c;
		end
		else
		begin
			Buffer.add_buffer buf rembuf;
			Buffer.add_char buf c;
			Buffer.clear rembuf
		end
	done;
	Buffer.add_buffer buf rembuf;
	Buffer.contents buf
;;
(* to remove: &#10; *)

let collectFromFile grrepr =
	let idmappings = ref RLMap.empty
	and resgraphnodes = ref (IdtMap.empty : nodeonpicturetype IdtMap.t)
	and resgraphedges = ref (IdtMap.empty : edgeonpicturetype IdtMap.t)
	in
	let (addResNode : nodeonpicturetype -> unit) = fun n -> resgraphnodes := IdtMap.add n.id n !resgraphnodes
	and addResEdge e = resgraphedges := IdtMap.add e.id e !resgraphedges
	in
	let idForStr s =
		try
			RLMap.find s !idmappings
		with Not_found -> begin
			let x = NewName.get ()
			in
			idmappings := RLMap.add s x !idmappings;
			x
		end
	in
	let collabxml = xmlchild grrepr "bpmn2:collaboration"
	in
	Xml.iter (fun collchild ->
		if Xml.tag collchild = "bpmn2:participant" then
		begin
			let nodeonpic = {
				id = idForStr (Xml.attrib collchild "processRef");
				kind = NOPPool;
				attrs = RLMap.singleton "name" (Xml.attrib collchild "name");
			}
			in
			addResNode nodeonpic
		end
		else if Xml.tag collchild = "bpmn2:messageFlow" then
		begin
			let isSecureChannel =
				let ll = xmlchilds collchild "pleak:SecureChannel"
				in
				(ll <> [])
			in
			print_string ("Message flow " ^ (Xml.attrib collchild "id") ^ " uses a secure channel: " ^ (string_of_bool isSecureChannel) ^ "\n" );
			let edgeonpic = {
				id = idForStr (Xml.attrib collchild "id");
				src = idForStr (Xml.attrib collchild "sourceRef");
				tgt = idForStr (try Xml.attrib collchild "targetRef" with Xml.No_attribute _ -> raise (Failure ("The msgFlow " ^ (Xml.attrib collchild "id") ^ " has no targetref")));
				kind = EOPMsgFlow;
				attrs = RLMap.singleton "securechannel" (if isSecureChannel then "true" else "false");
			}
			in
			addResEdge edgeonpic
		end
		else ()
	) collabxml;
	let xmlprocesses = xmlchilds grrepr "bpmn2:process"
	in
	let collectDataAssocs xmltask taskid =
		Xml.iter (fun childelem ->
			let childtag = Xml.tag childelem
			in
			if childtag = "bpmn2:dataOutputAssociation" then
			begin
				let refxml = try xmlchild childelem "bpmn2:targetRef" with Xml.No_attribute _ -> raise (Failure ("The dataout " ^ (Xml.attrib childelem "id") ^ " has no bpmn2:targetref"))
				in
				let dataobjidxml = getPCData refxml
				in
				let dataAssocEdge = {
					id = NewName.get ();
					tgt = idForStr dataobjidxml;
					src = taskid;
					kind = EOPWrite;
					attrs = RLMap.empty
				}
				in
				addResEdge dataAssocEdge
			end
			else if childtag = "bpmn2:dataInputAssociation" then
			begin
				let refxml = xmlchild childelem "bpmn2:sourceRef"
				in
				let dataobjidxml = getPCData refxml
				in
				let dataAssocEdge = {
					id = NewName.get ();
					src = idForStr dataobjidxml;
					tgt = taskid;
					kind = EOPRead;
					attrs = RLMap.empty
				}
				in
				addResEdge dataAssocEdge
			end
			else ()
		) xmltask
	and determineEventType xmlevent =
		let eventtype = ref "plain"
		in
		Xml.iter (fun childelem ->
			try
				let chname = Xml.tag childelem
				in
				if chname = "bpmn2:messageEventDefinition" then eventtype := "message"
				else if chname = "bpmn2:errorEventDefinition" then eventtype := "error"
				else if chname = "bpmn2:signalEventDefinition" then eventtype := "signal"
				else if chname = "bpmn2:timerEventDefinition" then eventtype := "timer"
				else ()
			with _ -> ()
		) xmlevent;
		!eventtype
	in
	let currentprocessname = ref ""
	in
	let rec handleprocess xmlprocess = (* here the process node has already been created *)
		let processid = idForStr (Xml.attrib xmlprocess "id")
		in
		let addHierEdge lowid =
			let hieredge = {
				id = NewName.get ();
				src = processid;
				tgt = lowid;
				kind = EOPContain;
				attrs = RLMap.empty;
			}
			in
			addResEdge hieredge
		in
		Xml.iter (fun xmlprocesselem ->
			let tagname = Xml.tag xmlprocesselem
			and elemname = try Some (Xml.attrib xmlprocesselem "name") with Xml.No_attribute _ -> None
			in
			let attrwithname = match elemname with None -> RLMap.empty | Some s -> RLMap.singleton "name" s
			in
			if (tagname = "bpmn2:startEvent") || (tagname = "bpmn2:intermediateThrowEvent") || (tagname = "bpmn2:intermediateCatchEvent") || (tagname = "bpmn2:endEvent") then
			begin
				let evkind = if tagname = "bpmn2:startEvent" then "start" else if tagname = "bpmn2:intermediateThrowEvent" then "throw" else if tagname = "bpmn2:intermediateCatchEvent" then "catch" else "end"
				in
				let nodeonpic = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPEvent;
					attrs = RLMap.add "eventtype" (determineEventType xmlprocesselem) (RLMap.add "eventkind" evkind attrwithname);
				}
				in
				addResNode nodeonpic;
				addHierEdge nodeonpic.id;
				collectDataAssocs xmlprocesselem nodeonpic.id
			end
			else if tagname = "bpmn2:boundaryEvent" then
			begin
				let nodeonpic = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPEvent;
					attrs = RLMap.add "eventtype" (determineEventType xmlprocesselem) (RLMap.add "eventkind" "boundary" attrwithname);
				}
				in
				addResNode nodeonpic;
				addHierEdge nodeonpic.id;
				let connEdge = {
					id = NewName.get ();
					src = idForStr (Xml.attrib xmlprocesselem "attachedToRef");
					tgt = nodeonpic.id;
					kind = EOPBoundary;
					attrs = RLMap.empty;
				}
				in
				addResEdge connEdge
			end
			else if (tagname = "bpmn2:task") || (tagname = "bpmn2:userTask") || (tagname = "bpmn2:sendTask") then
			begin
				let nodeonpic0 = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPTask;
					attrs = RLMap.add "tasktype" (if tagname = "bpmn2:userTask" then "user" else "plain") attrwithname;
				}
				in
				let tryToPickAttr xmlname parsename (nodeonpic : nodeonpicturetype) =
					try
						let xmlsql = xmlchild xmlprocesselem xmlname
						in
						let actualsql = getPCData xmlsql
						in
						if actualsql <> "" then
							{nodeonpic with attrs = RLMap.add parsename actualsql nodeonpic.attrs}
						else nodeonpic
					with Xml.No_attribute _ -> nodeonpic
				in
				let nodeonpic1 = tryToPickAttr "pleak:PKPublic" "pkpublic" (tryToPickAttr "pleak:PKPrivate" "pkprivate" (tryToPickAttr "pleak:PKDecrypt" "pkdecrypt" (tryToPickAttr "pleak:PKEncrypt" "pkencrypt" (tryToPickAttr "pleak:ABPublic" "abpublic" (tryToPickAttr "pleak:ABPrivate" "abprivate" (tryToPickAttr "pleak:ABDecrypt" "abdecrypt" (tryToPickAttr "pleak:ABEncrypt" "abencrypt" (tryToPickAttr "pleak:SKDecrypt" "skdecrypt" (tryToPickAttr "pleak:SKEncrypt" "skencrypt" (tryToPickAttr "pleak:sqlScript" "sql" nodeonpic0))))))))))
				in
				addResNode nodeonpic1;
				addHierEdge nodeonpic1.id;
				collectDataAssocs xmlprocesselem nodeonpic1.id
			end
			else if (tagname = "bpmn2:dataObjectReference") || (tagname = "bpmn2:dataStoreReference") then
			begin
				let tryToPickAttr xmlname parsename (nodeonpic : nodeonpicturetype) =
					try
						let xmlsql = xmlchild xmlprocesselem xmlname
						in
						let actualsql = getPCData xmlsql
						in
						if actualsql <> "" then
							{nodeonpic with attrs = RLMap.add parsename actualsql nodeonpic.attrs}
						else nodeonpic
					with Xml.No_attribute _ -> nodeonpic
				in
				let nodeonpic = tryToPickAttr "pleak:PKPublic" "pkpublic" (tryToPickAttr "pleak:PKPrivate" "pkprivate" (tryToPickAttr "pleak:ABPublic" "abpublic" (tryToPickAttr "pleak:ABPrivate" "abprivate" (tryToPickAttr "pleak:sqlScript" "sql" ({
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPDataset;
					attrs = (* RLMap.add "name" ((RLMap.find "name" attrwithscript) ^ " {" ^  !currentprocessname ^"}") *) if tagname = "bpmn2:dataStoreReference" then RLMap.add "datastore" "yes" attrwithname else attrwithname;
				})))))
				in
				addResNode nodeonpic;
				addHierEdge nodeonpic.id
			end
			else if tagname = "bpmn2:subProcess" then
			begin
				let nodeonpic0pre = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPSubprocess;
					attrs = attrwithname;
				}
				in
				let nodeonpic0 = if (RLMap.mem "name" nodeonpic0pre.attrs) && ((RLMap.find "name" nodeonpic0pre.attrs) <> "") then nodeonpic0pre else {nodeonpic0pre with attrs = RLMap.add "name" (Xml.attrib xmlprocesselem "id") nodeonpic0pre.attrs}
				in
				let nodeonpic1 =
					try
						let xmlrepeat = xmlchild xmlprocesselem "bpmn2:multiInstanceLoopCharacteristics"
						in
						let repeatkind =
							try
								ignore (Xml.attrib xmlrepeat "isSequential");
								"serial"
							with Xml.No_attribute _ -> "parallel"
						in
						{nodeonpic0 with attrs = RLMap.add "repeat" repeatkind nodeonpic0.attrs}
					with Xml.No_attribute _ -> nodeonpic0
				in
				addResNode nodeonpic1;
				addHierEdge nodeonpic1.id;
				handleprocess xmlprocesselem
			end
			else if (tagname = "bpmn2:sequenceFlow") || (tagname = "bpmn2:association") then
			begin
				let connEdge = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					src = idForStr (Xml.attrib xmlprocesselem "sourceRef");
					tgt = idForStr (try Xml.attrib xmlprocesselem "targetRef" with Xml.No_attribute _ -> raise (Failure ("The seqFlow or assoc " ^ (Xml.attrib xmlprocesselem "id") ^ " has no targetref")));
					kind = if tagname = "bpmn2:sequenceFlow" then EOPSeqFlow else EOPComment;
					attrs = attrwithname;
				}
				in
				addResEdge connEdge
			end
			else if tagname = "bpmn2:textAnnotation" then
			begin
				let textchild = xmlchild xmlprocesselem "bpmn2:text"
				in
				let comment = getPCData textchild
				in
				let nodeonpic = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPComment;
					attrs = RLMap.singleton "comment" comment;
				}
				in
				addResNode nodeonpic;
				addHierEdge nodeonpic.id
			end
			else if (tagname = "bpmn2:exclusiveGateway") || (tagname = "bpmn2:eventBasedGateway") || (tagname = "bpmn2:parallelGateway") then
			begin
				let attrwithdefault =
					try
						let defid = idForStr (Xml.attrib xmlprocesselem "default")
						in
						RLMap.add "default" (NewName.to_string defid) attrwithname
					with Xml.No_attribute _ -> attrwithname
					in
				let nodeonpic = {
					id = idForStr (Xml.attrib xmlprocesselem "id");
					kind = NOPGateway;
					attrs = RLMap.add "gatewaykind" (if tagname = "bpmn2:exclusiveGateway" then "exclusive" else if tagname = "bpmn2:parallelGateway" then "parallel" else "eventbased") attrwithdefault;
				}
				in
				addResNode nodeonpic;
				addHierEdge nodeonpic.id
			end
			else ()
		) xmlprocess
	in
	List.iter (fun prc -> 
		currentprocessname := Xml.attrib prc "id";
		handleprocess prc
	) xmlprocesses;
	let (outg, incom) = IdtMap.fold (fun edgeid edgerec (currout, currin) ->
		let sout = try IdtMap.find edgerec.src currout with Not_found -> IdtSet.empty
		and sin = try IdtMap.find edgerec.tgt currin with Not_found -> IdtSet.empty
		in
		(IdtMap.add edgerec.src (IdtSet.add edgeid sout) currout,
		IdtMap.add edgerec.tgt (IdtSet.add edgeid sin) currin)
	) !resgraphedges (IdtMap.empty, IdtMap.empty)
	in
	let revIdForStr nid = 
		RLMap.fold (fun k x res ->
			if x = nid then k else res
		) !idmappings "NONE"
	in
	IdtMap.iter (fun _ edgerec ->
		if (IdtMap.mem edgerec.src !resgraphnodes) && (IdtMap.mem edgerec.tgt !resgraphnodes) then () else
		begin
			print_string ("There is edge from " ^ (revIdForStr edgerec.src) ^ " to " ^ (revIdForStr edgerec.tgt) ^ "\n");
			(if not (IdtMap.mem edgerec.src !resgraphnodes) then print_string "The source is missing\n");
			(if not (IdtMap.mem edgerec.tgt !resgraphnodes) then print_string "The target is missing\n")
		end
	) !resgraphedges;
	let resnodestmp1 = IdtMap.merge (fun k x y -> match x,y with None,None -> None | Some xx,None -> Some (xx, IdtSet.empty) | Some xx, Some yy -> Some (xx,yy) | None, Some _ -> raise (Failure (revIdForStr k)) ) !resgraphnodes outg
	in
	let resnodestmp2 = IdtMap.merge (fun k x y -> match x,y with None,None -> None | Some (xx1,xx2), None -> Some (xx1,xx2, IdtSet.empty) | Some (xx1,xx2), Some yy -> Some (xx1,xx2,yy) | None, Some _ -> raise (Failure (revIdForStr k))) resnodestmp1 incom
	in
	let resnodestmp3 = IdtMap.map (fun ((nde : nodeonpicturetype),nout,nin) ->
		let nde' = if nde.kind = NOPPool then {nde with kind = NOPSubprocess} else nde
		in
		(nde', nout, nin)
	) resnodestmp2
	in
	let grrepr = {nodes = resnodestmp3; edges = !resgraphedges;}
	in
	let encupdnodes = IdtMap.map (fun ((nodeonpic1 : nodeonpicturetype),woutg,wincom) ->
		let nodeonpic2 = if (nodeonpic1.kind = NOPTask) then
		begin
			if ((RLMap.mem "skdecrypt" nodeonpic1.attrs) || (RLMap.mem "skencrypt" nodeonpic1.attrs)) then
			begin
				let (isEnc, jsondesc) = if RLMap.mem "skencrypt" nodeonpic1.attrs then (true, RLMap.find "skencrypt" nodeonpic1.attrs) else (false, RLMap.find "skdecrypt" nodeonpic1.attrs)
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let keyds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "key" js)
				and textds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member (if isEnc then "inputData" else "ciphertext") js)
				in
				let (keyNode,_,_) = IdtMap.find (idForStr keyds) grrepr.nodes
				and (textNode,_,_) = IdtMap.find (idForStr textds) grrepr.nodes
				in
				let keyname = RLMap.find "name" keyNode.attrs
				and textname = RLMap.find "name" textNode.attrs
				in
				{nodeonpic1 with attrs = RLMap.add "skkey" keyname (RLMap.add "sktext" textname nodeonpic1.attrs)}
			end
			else if RLMap.mem "abencrypt" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "abencrypt" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let keyds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "key" js)
				and textds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "inputData" js)
				and attrAsList = List.map Yojson.Basic.Util.to_string (Yojson.Basic.Util.to_list (Yojson.Basic.Util.member "attributeSubSet" js))
				in
				let (keyNode,_,_) = IdtMap.find (idForStr keyds) grrepr.nodes
				and (textNode,_,_) = IdtMap.find (idForStr textds) grrepr.nodes
				in
				let keyname = RLMap.find "name" keyNode.attrs
				and textname = RLMap.find "name" textNode.attrs
				in
				let nattrs1 = RLMap.add "abAttrNum" (string_of_int (List.length attrAsList)) (RLMap.add "abenckey" keyname (RLMap.add "abplaintext" textname nodeonpic1.attrs))
				in
				let nattrs2 = List.fold_right (fun (idx,s) m -> RLMap.add ("Attribute_" ^ (string_of_int idx)) s m) (List.mapi (fun idx s -> (idx,s)) attrAsList) nattrs1
				in
				{nodeonpic1 with attrs = nattrs2}
			end
			else if RLMap.mem "pkencrypt" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "pkencrypt" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let keyds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "key" js)
				and textds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "inputData" js)
				in
				let (keyNode,_,_) = IdtMap.find (idForStr keyds) grrepr.nodes
				and (textNode,_,_) = IdtMap.find (idForStr textds) grrepr.nodes
				in
				let keyname = RLMap.find "name" keyNode.attrs
				and textname = RLMap.find "name" textNode.attrs
				in
				let nattrs1 = RLMap.add "pkenckey" keyname (RLMap.add "pkplaintext" textname nodeonpic1.attrs)
				in
				{nodeonpic1 with attrs = nattrs1}
			end
			else if RLMap.mem "abdecrypt" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "abdecrypt" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let keyds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "key" js)
				and textds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "ciphertext" js)
				in
				let (keyNode,_,_) = IdtMap.find (idForStr keyds) grrepr.nodes
				and (textNode,_,_) = IdtMap.find (idForStr textds) grrepr.nodes
				in
				let keyname = RLMap.find "name" keyNode.attrs
				and textname = RLMap.find "name" textNode.attrs
				in
				{nodeonpic1 with attrs = RLMap.add "abdeckey" keyname (RLMap.add "abciphertext" textname nodeonpic1.attrs)}
			end
			else if RLMap.mem "pkdecrypt" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "pkdecrypt" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let keyds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "key" js)
				and textds = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "ciphertext" js)
				in
				let (keyNode,_,_) = IdtMap.find (idForStr keyds) grrepr.nodes
				and (textNode,_,_) = IdtMap.find (idForStr textds) grrepr.nodes
				in
				let keyname = RLMap.find "name" keyNode.attrs
				and textname = RLMap.find "name" textNode.attrs
				in
				{nodeonpic1 with attrs = RLMap.add "pkdeckey" keyname (RLMap.add "pkciphertext" textname nodeonpic1.attrs)}
			end
			else nodeonpic1
		end
		else if (nodeonpic1.kind = NOPDataset) then
		begin
			if RLMap.mem "abpublic" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "abpublic" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let groupid = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "groupId" js)
				in
				{nodeonpic1 with attrs = RLMap.add "abgroup" groupid nodeonpic1.attrs}
			end
			else if RLMap.mem "pkpublic" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "pkpublic" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let groupid = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "groupId" js)
				in
				{nodeonpic1 with attrs = RLMap.add "pkgroup" groupid nodeonpic1.attrs}
			end
			else if RLMap.mem "abprivate" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "abprivate" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let groupid = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "groupId" js)
				and attrAsList = List.map Yojson.Basic.Util.to_string (Yojson.Basic.Util.to_list (Yojson.Basic.Util.member "attributeSubSet" js))
				in
				let nattrs1 = RLMap.add "abAttrNum" (string_of_int (List.length attrAsList)) (RLMap.add "abgroup" groupid nodeonpic1.attrs)
				in
				let nattrs2 = List.fold_right (fun (idx,s) m -> RLMap.add ("Attribute_" ^ (string_of_int idx)) s m) (List.mapi (fun idx s -> (idx,s)) attrAsList) nattrs1
				in
				{nodeonpic1 with attrs = nattrs2}
			end
			else if RLMap.mem "pkprivate" nodeonpic1.attrs then
			begin
				let jsondesc = RLMap.find "pkprivate" nodeonpic1.attrs
				in
				let js = Yojson.Basic.from_string jsondesc
				in
				let groupid = Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "groupId" js)
				in
				let nattrs1 = RLMap.add "pkgroup" groupid nodeonpic1.attrs
				in
				{nodeonpic1 with attrs = nattrs1}
			end
			else nodeonpic1
		end else nodeonpic1
		in
		(nodeonpic2, woutg, wincom)
	) grrepr.nodes
	in
	({grrepr with nodes = encupdnodes}, idForStr)
;;

let commentsToAttrs grrepr =
	IdtMap.fold (fun nid ((ndesc : nodeonpicturetype), noutg, nincom) ngr ->
		if ndesc.kind = NOPComment then
		begin
			let comconnid = try grreprIncomingEdgeOfKind ngr nid EOPComment with Not_found -> NewName.invalid_id
			in
			if comconnid = NewName.invalid_id then grreprRemoveNode ngr nid else
			let comconn = IdtMap.find comconnid ngr.edges
			in
			let (srcn, srcoutg, srcincom) = IdtMap.find comconn.src ngr.nodes
			in
			let newsrcn = {srcn with attrs = RLMap.add "comment" (RLMap.find "comment" ndesc.attrs) srcn.attrs}
			in
			grreprRemoveNode (grreprAddNode ngr newsrcn) nid
		end else ngr
	) grrepr.nodes grrepr
;;

let noMultipleMsgflows grrepr =
	let storeOGMF = Hashtbl.create 10
	in
	IdtMap.fold (fun eid (edesc : edgeonpicturetype) ngr ->
		if edesc.kind <> EOPMsgFlow then ngr else
		if Hashtbl.mem storeOGMF edesc.src then grreprRemoveEdge ngr eid else
		(Hashtbl.add storeOGMF edesc.src (); ngr)
	) grrepr.edges grrepr
;;

let noMultipleWrites grrepr =
	let storeOGMF = Hashtbl.create 10
	in
	IdtMap.fold (fun eid (edesc : edgeonpicturetype) ngr ->
		if edesc.kind <> EOPWrite then ngr else
		if Hashtbl.mem storeOGMF (edesc.src,edesc.tgt) then grreprRemoveEdge ngr eid else
		(Hashtbl.add storeOGMF (edesc.src,edesc.tgt) (); ngr)
	) grrepr.edges grrepr
;;

let defaultsToEdgeAttrs (grrepr : graphgraphtype) =
	IdtMap.fold (fun nid ((ndesc : nodeonpicturetype), noutg, nincom) ngr ->
		if (ndesc.kind = NOPGateway) && ((RLMap.find "gatewaykind" ndesc.attrs) = "exclusive") then
		begin
			let defaultid = try NewName.from_string (RLMap.find "default" ndesc.attrs) with Not_found -> NewName.invalid_id
			in
			let newedgeset = IdtSet.fold (fun outedgeid curredgeset ->
				let outedge = IdtMap.find outedgeid curredgeset
				in
				if outedge.kind <> EOPSeqFlow then curredgeset else
				let updedgeattrs = (if outedge.id = defaultid then RLMap.add "branch" "false" else RLMap.add "branch" "true") outedge.attrs
				in
				IdtMap.add outedgeid {outedge with attrs = updedgeattrs} curredgeset
			) noutg ngr.edges
			in
			{ngr with edges = newedgeset}
		end
		else ngr
	) grrepr.nodes grrepr
;;

let lastCommonAncestor grrepr nid1 nid2 =
	let rec myAncestors nid =
		let (ndesc, noutps, ninps) = IdtMap.find nid grrepr.nodes
		in
		try
			let containingEdgeId = IdtSet.choose (IdtSet.filter (fun edgeid ->
				let edge = IdtMap.find edgeid grrepr.edges
				in
				edge.kind = EOPContain
			) ninps)
			in
			let cEdge = IdtMap.find containingEdgeId grrepr.edges
			in
			nid :: (myAncestors cEdge.src)
		with Not_found -> [nid]
	and lastCommon (x::xs) (y::ys) = match xs,ys with
		| [],_
		| _,[] -> x
		| (u::us), (v::vs) -> if u = v then lastCommon xs ys else x
	in
	let l1 = myAncestors nid1
	and l2 = myAncestors nid2
	in
	lastCommon (List.rev l1) (List.rev l2)
;;

let joinSameNameDatasets grrepr =
	let ds2id = ref RLMap.empty
	in
	IdtMap.fold (fun nid ((ndesc : nodeonpicturetype), nout, nincom) currgrrepr ->
		if ndesc.kind = NOPDataset then
		begin
			let datasetname = RLMap.find "name" ndesc.attrs
			in
			let origid = try RLMap.find datasetname !ds2id with Not_found -> nid
			in
			if origid = nid then (ds2id := RLMap.add datasetname nid !ds2id; currgrrepr) else
			begin
			let (currndesc, curroutps, currinps) = IdtMap.find nid currgrrepr.nodes
			in
			let grrepr1 = IdtSet.fold (fun edgeid tmpgrrepr ->
				let edge = IdtMap.find edgeid tmpgrrepr.edges
				in
				if edge.kind = EOPWrite then grreprMoveEdgeTarget tmpgrrepr edgeid origid else tmpgrrepr
			) currinps currgrrepr
			in
			let grrepr2 = IdtSet.fold (fun edgeid tmpgrrepr ->
				let edge = IdtMap.find edgeid tmpgrrepr.edges
				in
				if edge.kind = EOPRead then grreprMoveEdgeSource tmpgrrepr edgeid origid else tmpgrrepr
			) curroutps grrepr1
			in
			let ancId = lastCommonAncestor grrepr2 origid nid
			in
			let (orign, origoutps, originps) = IdtMap.find origid grrepr2.nodes
			in
			let grrepr3 = IdtSet.fold (fun edgeid tmpgrrepr ->
				let edge = IdtMap.find edgeid tmpgrrepr.edges
				in
				if edge.kind = EOPContain then grreprMoveEdgeSource tmpgrrepr edgeid ancId else tmpgrrepr
			) originps grrepr2
			in
			grreprRemoveNode grrepr3 nid
			end
		end
		else currgrrepr
	) grrepr.nodes grrepr
;;

let cutSequenceOverNode grrepr nodeid =
	let (node, outg, incom) = IdtMap.find nodeid grrepr.nodes
	in
	let gr1 = IdtSet.fold (fun outedgeid igr ->
		let outedge = IdtMap.find outedgeid igr.edges
		in
		if outedge.kind <> EOPSeqFlow then igr else
		IdtSet.fold (fun inedgeid iigr ->
			let inedge = IdtMap.find inedgeid iigr.edges
			in
			if inedge.kind <> EOPSeqFlow then iigr else
			let newedge = {
				id = NewName.get ();
				src = inedge.src;
				tgt = outedge.tgt;
				kind = EOPSeqFlow;
				attrs = RLMap.union outedge.attrs inedge.attrs;
			}
			in
			grreprAddEdge iigr newedge
		) incom igr
	) outg grrepr
	in
	IdtSet.fold (fun edgeid igr ->
		grreprRemoveEdge igr edgeid
	) (IdtSet.union outg incom) gr1
;;

let dissolveNonreplSubproc grrepr = (* Assumption: a single edge out of the start event, a single end event, and a single edge out of the process *)
	let isSuitableSubprocess ((ndesc : nodeonpicturetype), noutg, nincom) =
		let notTop = IdtSet.exists (fun eid -> let edesc = IdtMap.find eid grrepr.edges in edesc.kind = EOPContain) nincom
		and isProc = (ndesc.kind = NOPSubprocess)
		and isReplicated = RLMap.mem "repeat" ndesc.attrs
		in
		if not (isProc && notTop && (not isReplicated)) then false else true
	in
	IdtMap.fold (fun nid nrec currgrrepr ->
		if isSuitableSubprocess nrec then
		begin
			let startnodes = findProcessStartNodes currgrrepr nid
			and endnodes = findProcessEndNodes currgrrepr nid
			in
			let (endnodesByType, continue) = List.fold_right (fun enid (res,c) ->
				if (not c) then (res,c) else
				let (endnode,_,_) = IdtMap.find enid currgrrepr.nodes
				in
				if endnode.kind <> NOPEvent then (res, false) else
				let entype = RLMap.find "eventtype" endnode.attrs
				in
				if RLMap.mem entype res then (res,false) else ((RLMap.add entype enid res), true)
			) endnodes (RLMap.empty, true)
			in
			if ((List.length startnodes) <> 1) || (not continue) || (not (RLMap.mem "plain" endnodesByType)) then currgrrepr else
			let (startnode, startnoutg, startnincom) = IdtMap.find (List.hd startnodes) currgrrepr.nodes
(*			and (endnode, endnodeoutg, endnodeincom) = IdtMap.find (List.hd endnodes) currgrrepr.nodes *)
			in
			if (startnode.kind <> NOPEvent) then currgrrepr else
			let (currndesc, curroutg, currincom) = IdtMap.find nid currgrrepr.nodes
			in
			let gr1 = IdtSet.fold (fun proutedgeid gr' ->
				let proutedge = IdtMap.find proutedgeid gr'.edges
				in
				if proutedge.kind = EOPSeqFlow then
					grreprMoveEdgeSource gr' proutedgeid (RLMap.find "plain" endnodesByType)
				else if proutedge.kind = EOPBoundary then
				begin
					let (bnode,bnoutg,bnincom) = IdtMap.find proutedge.tgt gr'.nodes
					in
					let bnseqoutedgeid = grreprOutgoingEdgeOfKind gr' bnode.id EOPSeqFlow
					in
					let res = grreprRemoveNode (grreprMoveEdgeSource gr' bnseqoutedgeid (RLMap.find (RLMap.find "eventtype" bnode.attrs) endnodesByType)) bnode.id
					in
					(areEdgesOK res; res)
				end else gr'
			) curroutg currgrrepr
			in
			let gr2 = (areEdgesOK gr1; IdtSet.fold (fun prinedgeid gr' ->
				let prinedge = IdtMap.find prinedgeid gr'.edges
				in
				if prinedge.kind <> EOPSeqFlow then gr' else
				grreprMoveEdgeTarget gr' prinedgeid startnode.id
			) currincom gr1)
			in
			let gr3 = (print_endline "check gr2"; areEdgesOK gr2; if (RLMap.find "eventtype" startnode.attrs) = "plain" then
				grreprRemoveNode (cutSequenceOverNode gr2 startnode.id) startnode.id
			else
				let (sn',snog',snic') = IdtMap.find startnode.id gr2.nodes
				in
				{gr2 with nodes = IdtMap.add startnode.id ({sn' with attrs = RLMap.add "eventkind" "catch" sn'.attrs}, snog',snic') gr2.nodes}
			)
			in
			let gr4 = (print_endline "check gr3"; areEdgesOK gr3; RLMap.fold (fun evtype endnodeid gr' ->
				grreprRemoveNode (cutSequenceOverNode gr' endnodeid) endnodeid
			) endnodesByType gr3)
(*			if (RLMap.find "eventtype" endnode.attrs) = "plain" then
				grreprRemoveNode (cutSequenceOverNode gr3 endnode.id) endnode.id
			else
				let (en',enog',enic') = IdtMap.find endnode.id gr3.nodes
				in
				{gr3 with nodes = IdtMap.add endnode.id ({en' with attrs = RLMap.add "eventtype" "throw" en'.attrs}, enog',enic') grrepr.nodes}
*)			in
			let (prn, prog, prin) = (print_endline "check gr4"; areEdgesOK gr4; IdtMap.find nid gr4.nodes)
			in
			let parentprocid = List.hd (
				IdtSet.fold (fun incedgeid ll ->
					let incedge = IdtMap.find incedgeid gr4.edges
					in
					if incedge.kind = EOPContain then incedge.src :: ll else ll
				) prin []
			)
			in
			let gr5 = IdtSet.fold (fun contedgeid gr' ->
				let contedge = IdtMap.find contedgeid gr'.edges
				in
				if contedge.kind <> EOPContain then gr' else
				grreprMoveEdgeSource gr' contedgeid parentprocid
			) prog gr4
			in
			grreprRemoveNode gr5 nid
		end else currgrrepr
	) grrepr.nodes grrepr
;;

let moveMsgFlowToStartNode grrepr =
	IdtMap.fold (fun edgeid edgerec currgrrepr ->
		if edgerec.kind <> EOPMsgFlow then currgrrepr else
		let (mftgtn,_,_) = IdtMap.find edgerec.tgt currgrrepr.nodes
		in
		if mftgtn.kind <> NOPSubprocess then currgrrepr else
		let startnodeids = findProcessStartNodes currgrrepr mftgtn.id
		in
		if (List.length startnodeids) <> 1 then currgrrepr else
		let snid = List.hd startnodeids
		in
		grreprMoveEdgeTarget currgrrepr edgeid snid
	) grrepr.edges grrepr
;;

let oneEndOfEachType grrepr =
	IdtMap.fold (fun procid ((procn : nodeonpicturetype), procoutg, procincom) currgrrepr ->
		if procn.kind <> NOPSubprocess then currgrrepr else
		(* if IdtSet.is_empty procincom then currgrrepr else *) (* otherwise this is an outermost process *)
		let endidset = findProcessEndNodes currgrrepr procid
		in
		let byType = List.fold_right (fun endid m ->
			let (endn, endoutg, endincom) = IdtMap.find endid currgrrepr.nodes
			in
			if endn.kind <> NOPEvent then raise (Failure "A subprocess may only end with an event") else
			let s = RLMap.find "eventtype" endn.attrs
			in
			let ss = try RLMap.find s m with Not_found -> IdtSet.empty
			in
			RLMap.add s (IdtSet.add endid ss) m
		) endidset RLMap.empty
		in
		RLMap.fold (fun evtype evnodes grrepr1 ->
			if (IdtSet.cardinal evnodes) <= 1 then grrepr1 else
			let ngateway = {
				kind = NOPGateway;
				id = NewName.get ();
				attrs = RLMap.singleton "gatewaykind" "exclusive";
			}
			and nendnodeid = IdtSet.choose evnodes
			in
			let grrepr2 = grreprAddEdge (grreprAddNode grrepr1 ngateway) {id = NewName.get (); src = procid; tgt = ngateway.id; kind = EOPContain; attrs = RLMap.empty;}
			in
			let grrepr3 = IdtSet.fold (fun evnodeid grrepr4 ->
				let (_,_,evincom) = IdtMap.find evnodeid grrepr4.nodes
				in
				IdtSet.fold (fun incedgeid grrepr5 ->
					if (IdtMap.find incedgeid grrepr5.edges).kind = EOPSeqFlow then grreprMoveEdgeTarget grrepr5 incedgeid ngateway.id else grrepr5
				) evincom grrepr4
			) evnodes grrepr2
			in
			let grrepr6 = IdtSet.fold (fun endnid grrepr7 ->
				grreprRemoveNode grrepr7 endnid
			) (IdtSet.remove nendnodeid evnodes) grrepr3
			in
			grreprAddEdge grrepr6 {id = NewName.get (); src = ngateway.id; tgt = nendnodeid; kind = EOPSeqFlow; attrs = RLMap.empty;}
		) byType currgrrepr
	) grrepr.nodes grrepr
;;

let translateTaskScript scriptstr isGuard =
	let keywords = ["="; "("; ")"; ","; "!"; "."]
	and isemptystream ss = try Stream.empty ss; true with Stream.Failure -> false
	in
	(* let tkstream = Genlex.make_lexer keywords (Stream.of_string scriptstr) *)
	let tkstream = 
		let inpbuf = Lexing.from_string scriptstr
		in
		let tokenColl = ref []
		in
		(try
			while true do
				tokenColl := (PleakBpmnLexer.token inpbuf) :: !tokenColl
			done;
		with PleakBpmnLexer.Eof -> () );
		Stream.of_list (List.rev !tokenColl)
	in
	let parserabbrvs = ref RLMap.empty
	and previouslines = ref []
	and guardexpr = ref None
	in
	let readabbrv s = try RLMap.find s !parserabbrvs with Not_found -> s
	in
	let rec parseExpr () =
		let fstTok = Stream.next tkstream
		in
		match fstTok with
		| Genlex.Ident funordsname -> begin
			let dummy = Stream.next tkstream
			in
			if (match dummy with Genlex.Kwd _ -> false | _ -> true) then raise (Failure "Parse failure: expected a keyword near the start of an expression")
			else
			let Genlex.Kwd sndElem = dummy
			in
			if sndElem = "." then
				let dummy = Stream.next tkstream
				in
				if (match dummy with Genlex.Ident _ -> false | _ -> true) then raise (Failure "Parse failure: expected a field name after the dot")
				else
				let Genlex.Ident compname = dummy
				in
				DEVar (readabbrv funordsname, compname)
			else if sndElem = "(" then
			begin
				let exprargs = ref []
				in
				while (Stream.peek tkstream) <> Some (Genlex.Kwd ")") do
					let onearg = parseExpr ()
					in
					exprargs := onearg :: !exprargs;
					if (Stream.peek tkstream) = Some (Genlex.Kwd ",") then ignore (Stream.next tkstream)
				done;
				ignore (Stream.next tkstream);
				DEAppl (funordsname, List.rev !exprargs)
			end
			else raise (Failure "Parse failure: expected either dot or open parenthesis near the start of an expression")
		end
		| Genlex.Int x -> DEIntConst x
		| Genlex.Float x -> DEFloatConst x
		| Genlex.String x -> DEStringConst x
	in
	while not (isemptystream tkstream) do
		let fstTok = Stream.peek tkstream
		in
		match fstTok with
		| Some (Genlex.Kwd fstKwd) -> begin
			if fstKwd = "!" then
			begin
				ignore (Stream.next tkstream);
				let Genlex.Ident aliasstr = Stream.next tkstream
				in
				let Genlex.String origstr = Stream.next tkstream
				in
				parserabbrvs := RLMap.add aliasstr origstr !parserabbrvs;
			end
			else raise (Failure "Parse failure: wrong keyword at the beginning of line")
		end
		| Some (Genlex.Ident ldsaliasname) -> begin
			if isGuard then begin
				guardexpr := Some (parseExpr ())
			end
			else begin
				ignore (Stream.next tkstream);
				let ldsname = readabbrv ldsaliasname
				in
				let Genlex.Kwd x1 = Stream.next tkstream
				in
				if x1 = "." then
				begin
					let dummy = Stream.next tkstream
					in
					let Genlex.Ident lcompname = dummy
					in
					let Genlex.Kwd x2 = Stream.next tkstream
					in
					if x2 <> "=" then raise (Failure "Parse failure: expected equality sign") else
					let rhs = parseExpr ()
					in
					previouslines := ((ldsname, lcompname), rhs) :: !previouslines
				end
				else if x1 = "=" then
				begin
					let Genlex.Ident ldsalias2name = Stream.next tkstream
					in
					let ldsname2 = readabbrv ldsalias2name
					in
					previouslines := ((ldsname, "*"), DEVar (ldsname2, "*")) :: !previouslines
				end
				else
					raise (Failure "Parse failure: expected dot as the separator at LHS; or equals sign as a simple assignment")
			end
		end
	done;
	if isGuard then
		let Some res = !guardexpr
		in Right res 
	else Left !previouslines
;;

let replicateAfterReplicate grrepr =
	IdtMap.fold (fun fstprocid ((fstprocn : nodeonpicturetype), fstprocoutg, fstprocincom) currgrrepr ->
		if fstprocn.kind <> NOPSubprocess then currgrrepr else
		if IdtSet.is_empty fstprocincom then currgrrepr else
		let firstprocendnodeids = findProcessEndNodes currgrrepr fstprocid
		in
		let (res,_) = List.fold_right (fun firstprocendnodeid (gr0, handledNodes) ->
			let (firstprocendnode,_,firstprocendnodeincom) = IdtMap.find firstprocendnodeid gr0.nodes
			in
			let endingtype = RLMap.find "eventtype" firstprocendnode.attrs
			in
			let Some edgeoutofproc =
				if endingtype = "plain" then
					IdtSet.fold (fun edgeid res -> match res with
						| Some _ -> res
						| None ->
							(try
							let edge = IdtMap.find edgeid gr0.edges
							in
							if edge.kind = EOPSeqFlow then Some edge else None
							with Not_found -> None )
					) fstprocoutg None
				else
					IdtSet.fold (fun edgeid res -> match res with
						| Some _ -> res
						| None ->
							(try
							let edge = IdtMap.find edgeid gr0.edges
							in
							if edge.kind <> EOPBoundary then None else
							let (boundedvnode, boundedvoutg, _) = IdtMap.find edge.tgt gr0.nodes
							in
							if (RLMap.find "eventtype" boundedvnode.attrs) <> endingtype then None else
							Some (IdtMap.find (IdtSet.choose boundedvoutg) gr0.edges)
							with Not_found -> None)
					) fstprocoutg None
			in
			let (followtaskandevids, stopnow) =
			begin
				let exploreedges = Queue.create ()
				and foundnodeids = ref IdtSet.empty
				and unsuitable = ref false
				in
				Queue.add edgeoutofproc exploreedges;
				while (not (Queue.is_empty exploreedges)) && (not !unsuitable) do
					let oneedge = Queue.take exploreedges
					in
					if IdtSet.mem oneedge.tgt !foundnodeids then () else
					begin
						foundnodeids := IdtSet.add oneedge.tgt !foundnodeids;
						let (fnode, fnoutg, _) = IdtMap.find oneedge.tgt gr0.nodes
						in
						(if fnode.kind = NOPSubprocess then unsuitable := true);
						IdtSet.iter (fun fnoutedgeid ->
							let fnoutedge = IdtMap.find fnoutedgeid gr0.edges
							in
							if fnoutedge.kind = EOPSeqFlow then Queue.add fnoutedge exploreedges
						) fnoutg
					end
				done;
				(!foundnodeids, !unsuitable)
			end
			in
			if stopnow then (gr0, handledNodes) else
			if (IdtSet.inter handledNodes followtaskandevids) <> IdtSet.empty then
				let nodelist = String.concat ", " (List.map NewName.to_string (IdtSet.elements (IdtSet.inter handledNodes followtaskandevids)))
				in
				begin raise (Failure ("The branches following a subprocess will merge somewhere down the line. Offending nodes: " ^ nodelist))
			end else
			let (followdataids,_) = IdtSet.fold (fun followtaskevid (gooddataids, alldataids) ->
				let (ften, fteog, fteinc) = IdtMap.find followtaskevid gr0.nodes
				in
				let goThroughEdgeIdSet getdatanodeid =
					IdtSet.fold (fun eid (goodids, allids) ->
						let edge = IdtMap.find eid gr0.edges
						in
						if (edge.kind <> EOPRead) && (edge.kind <> EOPWrite) then (goodids, allids) else
						let datanodeid = getdatanodeid edge
						in
						if IdtSet.mem datanodeid allids then (goodids, allids) else
						let (datanode, dnog, dninc) = IdtMap.find datanodeid gr0.nodes
						in
						if (IdtSet.for_all (fun dneid ->
							let dne = IdtMap.find dneid gr0.edges
							in
							(dne.kind <> EOPRead) || (IdtSet.mem dne.tgt followtaskandevids)
						) dnog) && (IdtSet.for_all (fun dneid ->
							let dne = IdtMap.find dneid gr0.edges
							in
							(dne.kind <> EOPWrite) || (IdtSet.mem dne.src followtaskandevids)
						) dninc) then (IdtSet.add datanodeid goodids, IdtSet.add datanodeid allids) else (goodids, IdtSet.add datanodeid allids)
					)
				in
				goThroughEdgeIdSet (fun e -> e.tgt) fteog (goThroughEdgeIdSet (fun e -> e.src) fteinc (gooddataids, alldataids))
			) followtaskandevids (IdtSet.empty, IdtSet.empty)
			in
			let (nowprocn, nowprocoutg, nowprocincom) = IdtMap.find fstprocid gr0.nodes
			in
			let Some parenprocid = IdtSet.fold (fun incedgeid res ->
				match res with
				| Some _ -> res
				| None ->
					let incedge = IdtMap.find incedgeid gr0.edges
					in
					if incedge.kind = EOPContain then Some incedge.src else None
			) nowprocincom None
			in
			let newprocn = {
				id = NewName.get ();
				kind = NOPSubprocess;
				attrs = RLMap.add "name" (endingtype ^ " followup of " ^ (RLMap.find "name" nowprocn.attrs)) (RLMap.singleton "repeat" "parallel");
			}
			and newstartnode = {
				id = NewName.get ();
				kind = NOPEvent;
				attrs = RLMap.add "name" (endingtype ^ " followup of " ^ (RLMap.find "name" nowprocn.attrs)) (RLMap.add "eventtype" "message" (RLMap.singleton "eventkind" "start"));
			}
			in
			let dummydatarecv = {
				id = NewName.get ();
				kind = NOPDataset;
				attrs = RLMap.singleton "name" ("catch_" ^ (NewName.to_string newstartnode.id));
			}
			in
			let startncontainedge = {
				id = NewName.get ();
				src = newprocn.id;
				tgt = newstartnode.id;
				kind = EOPContain;
				attrs = RLMap.empty;
			}
			and newproccontainedge = {
				id = NewName.get ();
				src = parenprocid;
				tgt = newprocn.id;
				kind = EOPContain;
				attrs = RLMap.empty;
			}
			and datarecvcontainedge = {
				id = NewName.get ();
				src = newprocn.id;
				tgt = dummydatarecv.id;
				kind = EOPContain;
				attrs = RLMap.empty;
			}
			and datarecvconnectedge = {
				id = NewName.get ();
				src = newstartnode.id;
				tgt = dummydatarecv.id;
				kind = EOPWrite;
				attrs = RLMap.empty;
			}
			in
			let gr1 = grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddNode (grreprAddNode (grreprAddNode gr0 newprocn) newstartnode) dummydatarecv) startncontainedge) newproccontainedge) datarecvcontainedge) datarecvconnectedge
			in
			let gr2 = grreprMoveEdgeSource (IdtSet.fold (fun procelemid gr' ->
				let ceid = grreprIncomingEdgeOfKind gr' procelemid EOPContain
				in
				grreprMoveEdgeSource gr' ceid newprocn.id
			) (IdtSet.union followtaskandevids followdataids) gr1) edgeoutofproc.id newstartnode.id
			in
			let dummydatasend = {
				id = NewName.get ();
				kind = NOPDataset;
				attrs = RLMap.singleton "name" ("throw_" ^ (NewName.to_string newstartnode.id));
			}
			and dummydatasender = {
				id = NewName.get ();
				kind = NOPTask;
				attrs = RLMap.singleton "name" "Send";
			}
			and dummydatainitializer = {
				id = NewName.get ();
				kind = NOPTask;
				attrs = RLMap.add "sql" ("throw_" ^ (NewName.to_string newstartnode.id) ^ ".v = \"DUMMY\"") (RLMap.singleton "name" ("Intialize throw_" ^ (NewName.to_string newstartnode.id)));
			}
			in
			let datasendcontainedge = {
				id = NewName.get ();
				src = fstprocid;
				tgt = dummydatasend.id;
				kind = EOPContain;
				attrs = RLMap.empty;
			}
			and datasendingedge = {
				id = NewName.get ();
				src = dummydatasend.id;
				tgt = dummydatasender.id;
				kind = EOPRead;
				attrs = RLMap.empty;
			}
			and msgflowedge = {
				id = NewName.get ();
				src = dummydatasender.id;
				tgt = newstartnode.id;
				kind = EOPMsgFlow;
				attrs = RLMap.singleton "securechannel" "true";
			}
			and datainitializingedge = {
				id = NewName.get ();
				src = dummydatainitializer.id;
				tgt = dummydatasend.id;
				kind = EOPWrite;
				attrs = RLMap.empty;
			}
			in
			let gr2a = grreprPutTaskToSeqFlow gr2 (grreprIncomingEdgeOfKind gr2 firstprocendnodeid EOPSeqFlow) dummydatasender
			in
			let gr3 = grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddNode (grreprPutTaskToSeqFlow gr2a (grreprIncomingEdgeOfKind gr2a dummydatasender.id EOPSeqFlow) dummydatainitializer) dummydatasend) datasendcontainedge) datasendingedge) msgflowedge) datainitializingedge
			in
			let gr4 = if endingtype = "plain" then gr3 else
				let Some boundaryEventId = IdtSet.fold (fun bedgeid res ->
					match res with
					| Some _ -> res
					| None ->
						let bedge = IdtMap.find bedgeid gr3.edges
						in
						if bedge.kind <> EOPBoundary then None else
						let (bnode,_,_) = IdtMap.find bedge.tgt gr3.nodes
						in
						if (RLMap.find "eventtype" bnode.attrs) <> endingtype then None else Some bedge.tgt
				) nowprocoutg None
				in
				grreprRemoveNode gr3 boundaryEventId
			in
			let edgetofstprocid = grreprIncomingEdgeOfKind gr4 fstprocid EOPSeqFlow
			in
			let gwnode = {
				id = NewName.get ();
				kind = NOPGateway;
				attrs = RLMap.singleton "gatewaykind" "parallel";
			}
			in
			let outedge = {
				id = NewName.get ();
				kind = EOPSeqFlow;
				src = gwnode.id;
				tgt = newprocn.id;
				attrs = RLMap.empty;
			}
			in
			(grreprAddEdge (grreprPutTaskToSeqFlow gr4 edgetofstprocid gwnode) outedge, IdtSet.union handledNodes followtaskandevids)
		) firstprocendnodeids (currgrrepr, IdtSet.empty)
		in
		res
	) grrepr.nodes grrepr
;;

let foldParallelParallelGW grrepr =
	IdtMap.fold (fun edgeid _ currgrrepr ->
		let edgerec = IdtMap.find edgeid currgrrepr.edges
		in
		if edgerec.kind <> EOPSeqFlow then currgrrepr else
		let (srcn, _, _) = IdtMap.find edgerec.src currgrrepr.nodes
		and (tgtn, tgtoutg, _) = IdtMap.find edgerec.tgt currgrrepr.nodes
		in
		if (srcn.kind = NOPGateway) && (tgtn.kind = NOPGateway) && ((RLMap.find "gatewaykind" srcn.attrs) = "parallel") && ((RLMap.find "gatewaykind" tgtn.attrs) = "parallel") then
			let gr1 = IdtSet.fold (fun outedgeid gr' ->
				let outedge = IdtMap.find outedgeid gr'.edges
				in
				if outedge.kind = EOPSeqFlow then
					grreprMoveEdgeSource gr' outedgeid srcn.id
				else gr'
			) tgtoutg currgrrepr
			in
			grreprRemoveNode gr1 tgtn.id
		else currgrrepr
	) grrepr.edges grrepr
;;

let replicateFollowsReplicate grrepr =
	let anychange = ref false
	in
	let procendingtypes grrepr procoutg =
		IdtSet.fold (fun bdedgeid ss ->
			let bdedge = IdtMap.find bdedgeid grrepr.edges
			in
			if bdedge.kind <> EOPBoundary then ss else
			let (bdevent,_,_) = IdtMap.find bdedge.tgt grrepr.nodes
			in
			RLSet.add (RLMap.find "eventtype" bdevent.attrs) ss
		) procoutg RLSet.empty
	in
	let resgr = IdtMap.fold (fun procid ((procn : nodeonpicturetype),_,procincom) currgrrepr ->
		if procn.kind <> NOPSubprocess then currgrrepr else
		if IdtSet.is_empty procincom then currgrrepr else
		if (not (IdtMap.mem procid currgrrepr.nodes)) then currgrrepr else
		let (procn, procoutg, procincom) = IdtMap.find procid currgrrepr.nodes
		in
		let Some (startnode, startnoutg, startnincom) = IdtSet.fold (fun outedgeid res ->
			match res with
			| Some _ -> res
			| None ->
				let outedge = IdtMap.find outedgeid currgrrepr.edges
				in
				let (possn, possoutg, possincom) = IdtMap.find outedge.tgt currgrrepr.nodes
				in
				if (possn.kind = NOPEvent) && ((RLMap.find "eventkind" possn.attrs) = "start") then
					Some (possn, possoutg, possincom)
				else None
		) procoutg None
		in
		if (RLMap.find "eventtype" startnode.attrs) <> "message" then currgrrepr else
		let msgflowedgeidl = IdtSet.fold (fun incomedgeid ll ->
			let incomedge = IdtMap.find incomedgeid currgrrepr.edges
			in
			if incomedge.kind = EOPMsgFlow then incomedgeid :: ll else ll
		) startnincom []
		in
		if (List.length msgflowedgeidl) <> 1 then currgrrepr else
		let msgflowedgeid = List.hd msgflowedgeidl
		in
		let msgflowedge = IdtMap.find msgflowedgeid currgrrepr.edges
		in
		let (msgsourcenode, msgsourceoutg, msgsourceincom) = IdtMap.find msgflowedge.src currgrrepr.nodes
		in
		let msgsourcecontainedgeid = grreprIncomingEdgeOfKind currgrrepr msgsourcenode.id EOPContain
		in
		let msgsourceprocid = (IdtMap.find msgsourcecontainedgeid currgrrepr.edges).src
		in
		let (msgsourceprocn, msgsourceprocoutg, msgsourceprocincom) = IdtMap.find msgsourceprocid currgrrepr.nodes
		in
		if IdtSet.is_empty msgsourceprocincom then currgrrepr else
		let procincomedgeid = grreprIncomingEdgeOfKind currgrrepr procid EOPSeqFlow
		and msgprocincomeedgeid = grreprIncomingEdgeOfKind currgrrepr msgsourceprocid EOPSeqFlow
		in
		let procincomeedge = IdtMap.find procincomedgeid currgrrepr.edges
		and msgprocincomeedge = IdtMap.find msgprocincomeedgeid currgrrepr.edges
		in
		if procincomeedge.src <> msgprocincomeedge.src then currgrrepr else
		let (paralgwnode, paralgwoutg, paralgwincom) = IdtMap.find procincomeedge.src currgrrepr.nodes
		in
		if (paralgwnode.kind <> NOPGateway) || ((RLMap.find "gatewaykind" paralgwnode.attrs) <> "parallel") then currgrrepr else
		let possEndNodeId = 
			let currPosition = ref msgsourcenode.id
			and makestep = ref true
			and foundEndNode = ref false
			in
			while !makestep do
				let (cpnode, cpoutg, _) = IdtMap.find !currPosition currgrrepr.nodes
				in
				if (cpnode.kind = NOPEvent) && ((RLMap.find "eventkind" cpnode.attrs) = "end") then
				begin
					foundEndNode := true;
					makestep := false
				end
				else
				begin
					let outseqflow = IdtSet.fold (fun outedgeid ll ->
						let outedge = IdtMap.find outedgeid currgrrepr.edges
						in
						if outedge.kind = EOPSeqFlow then outedge.tgt :: ll else ll
					) cpoutg []
					and numoutmsgflow = IdtSet.fold (fun outedgeid x ->
						let outedge = IdtMap.find outedgeid currgrrepr.edges
						in
						if outedge.kind = EOPMsgFlow then x+1 else x
					) cpoutg 0
					in
					if ((List.length outseqflow) = 1) && (numoutmsgflow > 0) then
					begin
						currPosition := List.hd outseqflow
					end
					else
					begin
						makestep := false
					end
				end
			done;
			if !foundEndNode then Some !currPosition else None
		in
		if possEndNodeId = None then currgrrepr else
		let Some endnodeid = possEndNodeId
		in
		let (endnode, endnodeoutg, endnodeincom) = IdtMap.find endnodeid currgrrepr.nodes
		in
		let endeventtype = RLMap.find "eventtype" endnode.attrs
		in
		if not (RLSet.is_empty (RLSet.remove endeventtype (procendingtypes currgrrepr msgsourceprocoutg)) ) then currgrrepr else
		let gr0 = if endeventtype = "plain" then currgrrepr else
			IdtSet.fold (fun proutedgeid gr' ->
				let proutedge = IdtMap.find proutedgeid gr'.edges
				in
				if proutedge.kind <> EOPBoundary then gr' else
				let (bdevent,_,_) = IdtMap.find proutedge.tgt gr'.nodes
				in
				if (RLMap.find "eventtype" bdevent.attrs) <> endeventtype then gr' else
				grreprRemoveNode gr' proutedge.tgt
			) msgsourceprocoutg currgrrepr
		in
		let gr1 = IdtSet.fold (fun proutedgeid gr' ->
			grreprMoveEdgeSource gr' proutedgeid msgsourceprocid
		) procoutg gr0
		in
		let connectionedge = {
			id = NewName.get ();
			src = endnodeid;
			tgt = startnode.id;
			kind = EOPSeqFlow;
			attrs = RLMap.empty;
		}
		in
		let gr2 = grreprAddEdge gr1 connectionedge
		in
		let newstartnode = {startnode with attrs = RLMap.add "eventkind" "catch" startnode.attrs}
		in
		let (_, stnoutg, stnincom) = IdtMap.find startnode.id gr2.nodes
		in
		let gr3 = {gr2 with nodes = IdtMap.add startnode.id (newstartnode, stnoutg, stnincom) gr2.nodes}
		in
		let gr4 = grreprRemoveNode (grreprRemoveNode (cutSequenceOverNode gr3 endnodeid) endnodeid) procid
		in
		(anychange := true; gr4)
	) grrepr.nodes grrepr
	in (resgr, !anychange)
;;

let conditionalTwoMsgReceive grrepr =
	IdtMap.fold (fun condgwid ((condgwn : nodeonpicturetype), cgwoutg, cgwincom) currgrrepr ->
		if (condgwn.kind <> NOPGateway) || ((RLMap.find "gatewaykind" condgwn.attrs) <> "eventbased") then currgrrepr else
		let (condgwn, cgwoutg, cgwincom) = IdtMap.find condgwid currgrrepr.nodes
		in
		let procid = (IdtMap.find (grreprIncomingEdgeOfKind currgrrepr condgwid EOPContain) currgrrepr.edges).src
		in
		let (controllednodeids, onlymsgcatch) = IdtSet.fold (fun edgeid (ll, b) ->
			if not b then ([], false) else
			let edge = IdtMap.find edgeid currgrrepr.edges
			in
			if edge.kind <> EOPContain then (ll, b) else
			let (node,_,_) = IdtMap.find edge.tgt currgrrepr.nodes
			in
			if (node.kind <> NOPEvent) || ((RLMap.find "eventkind" node.attrs) <> "catch") || ((RLMap.find "eventtype" node.attrs) <> "message") then ([], false) else
			(edge.tgt :: ll, b)
		) cgwoutg ([], true)
		in
		if not onlymsgcatch then currgrrepr else
		let arrofcntrldids = Array.of_list controllednodeids
		in
		let arrofafterids = Array.map (fun controlledid ->
			(IdtMap.find (grreprOutgoingEdgeOfKind currgrrepr controlledid EOPSeqFlow) currgrrepr.edges).tgt
		) arrofcntrldids
		in
		let condplacename = "record_condition_place_" ^ (NewName.to_string condgwid)
		in
		let condplacenode = {
			id = NewName.get ();
			kind = NOPDataset;
			attrs = RLMap.add "sql" "idx : integer" (RLMap.singleton "name" condplacename);
		}
		in
		let condplacecontainedge = {
			id = NewName.get ();
			src = procid;
			tgt = condplacenode.id;
			kind = EOPContain;
			attrs = RLMap.empty;
		}
		in
		let gr0 = grreprAddEdge (grreprAddNode currgrrepr condplacenode) condplacecontainedge
		in
		let resettask = {
			id = NewName.get ();
			kind = NOPTask;
			attrs = RLMap.add "sql" (condplacename ^ ".idx = 0") (RLMap.singleton "name" ("Reset indicator for " ^ NewName.to_string condgwid));
		}
		in
		let resetwriteedge = {
			id = NewName.get ();
			kind = EOPWrite;
			src = resettask.id;
			tgt = condplacenode.id;
			attrs = RLMap.empty;
		}
		in
		let gr1 = grreprAddEdge (grreprPutTaskToSeqFlow gr0 (grreprIncomingEdgeOfKind gr0 condgwid EOPSeqFlow) resettask) resetwriteedge
		in
		let paralgateway = {
			id = NewName.get ();
			kind = NOPGateway;
			attrs = RLMap.singleton "gatewaykind" "parallel";
		}
		in
		let gr2 = grreprPutTaskToSeqFlow gr1 (grreprIncomingEdgeOfKind gr1 condgwid EOPSeqFlow) paralgateway
		in
		let (gr3,_) = Array.fold_right (fun controllednodeid (gr', idxwrite) ->
			let intocatchedge = {
				id = NewName.get ();
				kind = EOPSeqFlow;
				src = paralgateway.id;
				tgt = controllednodeid;
				attrs = RLMap.empty;
			}
			in
			let gr'' = grreprAddEdge gr' intocatchedge
			in
			let updatecondplacenode = {
				id = NewName.get ();
				kind = NOPTask;
				attrs = RLMap.add "sql" (condplacename ^ ".idx = " ^ (string_of_int idxwrite)) (RLMap.singleton "name" ("update " ^ condplacename ^ " to " ^ (string_of_int idxwrite)));
			}
			in
			let updatecondplaceedge = {
				id = NewName.get ();
				kind = EOPWrite;
				src = updatecondplacenode.id;
				tgt = condplacenode.id;
				attrs = RLMap.empty;
			}
			in
			let gr3' = grreprAddEdge (grreprPutTaskToSeqFlow gr'' (grreprOutgoingEdgeOfKind gr'' controllednodeid EOPSeqFlow) updatecondplacenode) updatecondplaceedge
			in
			let endevent = {
				id = NewName.get ();
				kind = NOPEvent;
				attrs = RLMap.add "eventtype" "plain" (RLMap.singleton "eventkind" "end");
			}
			in
			let gr4' = grreprPutTaskToSeqFlow gr3' (grreprOutgoingEdgeOfKind gr3' updatecondplacenode.id EOPSeqFlow) endevent
			in
			(grreprRemoveEdge gr4' (grreprOutgoingEdgeOfKind gr4' endevent.id EOPSeqFlow), idxwrite - 1)
		) arrofcntrldids (gr2, Array.length arrofcntrldids)
		in
		let currgr = ref gr3
		in
		Array.iteri (fun idx afterid ->
			let guardtasknode = {
				id = NewName.get ();
				kind = NOPTask;
				attrs = RLMap.add "sql" ("equals(" ^ condplacename ^ ".idx, " ^ (string_of_int (idx+1)) ^ ")") (RLMap.singleton "name" ("Check " ^ condplacename ^ " for " ^ (string_of_int (idx+1))));
			}
			in
			currgr := grreprPutTaskToSeqFlow !currgr (grreprIncomingEdgeOfKind !currgr condgwid EOPSeqFlow) guardtasknode;
			let gatewaynode = {
				id = NewName.get ();
				kind = NOPGateway;
				attrs = RLMap.singleton "gatewaykind" "exclusive";
			}
			in
			currgr := grreprPutTaskToSeqFlow !currgr (grreprIncomingEdgeOfKind !currgr condgwid EOPSeqFlow) gatewaynode;
			let falseedgeid = grreprIncomingEdgeOfKind !currgr condgwid EOPSeqFlow
			in
			let falseedge = IdtMap.find falseedgeid !currgr.edges
			in
			currgr := {!currgr with edges = IdtMap.add falseedgeid {falseedge with attrs = RLMap.add "branch" "false" falseedge.attrs} !currgr.edges};
			let trueedge = {
				id = NewName.get ();
				kind = EOPSeqFlow;
				src = gatewaynode.id;
				tgt = afterid;
				attrs = RLMap.singleton "branch" "true";
			}
			in
			currgr := grreprAddEdge !currgr trueedge
		) arrofafterids;
		let endevent = {
			id = NewName.get ();
			kind = NOPEvent;
			attrs = RLMap.add "eventtype" "plain" (RLMap.singleton "eventkind" "end");
		}
		in
		currgr := grreprPutTaskToSeqFlow !currgr (grreprIncomingEdgeOfKind !currgr condgwid EOPSeqFlow) endevent;
		grreprRemoveNode !currgr condgwid
	) grrepr.nodes grrepr
;;

let copyBeforeSend grrepr =
	IdtMap.fold (fun sendTaskId ((sendTaskN : nodeonpicturetype), stoutg, stincom) currgrrepr ->
		if sendTaskN.kind <> NOPTask then currgrrepr else
		if IdtSet.for_all (fun outedgeid ->
			let outedge = IdtMap.find outedgeid currgrrepr.edges
			in
			outedge.kind <> EOPMsgFlow
		) stoutg then currgrrepr else
		let dataedgeid = grreprIncomingEdgeOfKind currgrrepr sendTaskId EOPRead
		in
		let dataedge = IdtMap.find dataedgeid currgrrepr.edges
		in
		let (datanode, dnoutg, dnincom) = IdtMap.find dataedge.src currgrrepr.nodes
		in
		let dataname = RLMap.find "name" datanode.attrs
		in
		let dncname = "Copy_of_" ^ dataname ^ "_for_send_no_" ^ (NewName.to_string sendTaskId)
		in
		let containingEdgeId = grreprIncomingEdgeOfKind currgrrepr sendTaskId EOPContain
		in
		let containingEdge = IdtMap.find containingEdgeId currgrrepr.edges
		in
		let newtask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" (dncname ^ ".* = " ^ dataname ^ ".*") (RLMap.singleton "name" "copy before send");
		}
		and newdata = {
			kind = NOPDataset;
			id = NewName.get ();
			attrs = RLMap.singleton "name" dncname;
		}
		in
		let newdataContain = {
			kind = EOPContain;
			id = NewName.get ();
			src = containingEdge.src;
			tgt = newdata.id;
			attrs = RLMap.empty;
		}
		and newdataWrite = {
			kind = EOPWrite;
			id = NewName.get ();
			src = newtask.id;
			tgt = newdata.id;
			attrs = RLMap.empty;
		}
		and olddataRead = {
			kind = EOPRead;
			id = NewName.get ();
			src = datanode.id;
			tgt = newtask.id;
			attrs = RLMap.empty;
		}
		in
		let gr1 = grreprPutTaskToSeqFlow currgrrepr (grreprIncomingEdgeOfKind currgrrepr sendTaskId EOPSeqFlow) newtask
		in
		let gr2 = grreprAddNode gr1 newdata
		in
		let gr3 = grreprAddEdge (grreprAddEdge (grreprAddEdge gr2 newdataContain) newdataWrite) olddataRead
		in
		grreprMoveEdgeSource gr3 dataedgeid newdata.id
	) grrepr.nodes grrepr
;;

let handle2ndtryConstellation grrepr =
	IdtMap.fold (fun sndProcId ((sndProcN : nodeonpicturetype), sndProcOutg, sndProcIncom) currgrrepr ->
		if sndProcN.kind <> NOPSubprocess then currgrrepr else
		if IdtSet.is_empty sndProcIncom then currgrrepr else
		let (sndProcN, sndProcOutg, sndProcIncom) = IdtMap.find sndProcId currgrrepr.nodes
		in
		let Some (startNode, startOutg, startIncom) = IdtSet.fold (fun outedgeid res ->
			match res with
			| Some _ -> res
			| None ->
				let outedge = IdtMap.find outedgeid currgrrepr.edges
				in
				let (possn, possoutg, possincom) = IdtMap.find outedge.tgt currgrrepr.nodes
				in
				if (possn.kind = NOPEvent) && ((RLMap.find "eventkind" possn.attrs) = "start") then
					Some (possn, possoutg, possincom)
				else None
		) sndProcOutg None
		in
		if (RLMap.find "eventtype" startNode.attrs) <> "message" then currgrrepr else
		let condgateways = IdtSet.fold (fun cntedgeid ll ->
			let cntedge = IdtMap.find cntedgeid currgrrepr.edges
			in
			if cntedge.kind <> EOPContain then ll else
			let (cndn, cndout, cndin) = IdtMap.find cntedge.tgt currgrrepr.nodes
			in
			if (cndn.kind = NOPGateway) && ((RLMap.find "gatewaykind" cndn.attrs) = "eventbased") then (cndn, cndout, cndin) :: ll else ll
		) sndProcOutg []
		in
		if (List.length condgateways) <> 1 then currgrrepr else
		let (condGatewayNode, condGatewayOutg, condGatewayIncom) = List.hd condgateways
		in
		let (timerevents, otherevents,isgood) = IdtSet.fold (fun seqedgeid (ll1,ll2,bb) ->
			if (not bb) then ([],[],false) else
			let seqedge = IdtMap.find seqedgeid currgrrepr.edges
			in
			if seqedge.kind <> EOPSeqFlow then (ll1,ll2,bb) else
			let
			(eventnode,evog,evinc) = IdtMap.find seqedge.tgt currgrrepr.nodes
			in
			if eventnode.kind <> NOPEvent then ([],[],false) else
			if (RLMap.find "eventkind" eventnode.attrs) <> "catch" then ([],[],false) else
			if (RLMap.find "eventtype" eventnode.attrs) = "timer" then (((eventnode,evog,evinc) :: ll1), ll2, true) else (ll1, ((eventnode,evog,evinc) :: ll2), true)
		) condGatewayOutg ([],[],true)
		in
		if (not isgood) || ((List.length timerevents) <> 1) || ((List.length otherevents) <> 1) then currgrrepr else
		let (timerEvNode,timerEvOg,timerEvInc) = List.hd timerevents
		and (otherEvNode,otherEvOg,otherEvInc) = List.hd otherevents
		in
		let evWrittenStates = IdtSet.fold (fun wredgeid ll ->
			let wredge = IdtMap.find wredgeid currgrrepr.edges
			in
			if wredge.kind = EOPWrite then wredge.tgt :: ll else ll
		) otherEvOg []
		in
		if (match evWrittenStates with _ :: [] -> false | _ -> true) then currgrrepr else
		let evWrittenStateId = List.hd evWrittenStates
		in
		let othereventtype = RLMap.find "eventtype" otherEvNode.attrs
		in
		let (prevtimevents, prevothevents, isgood) = IdtSet.fold (fun seqedgeid (ll1,ll2,bb) ->
			if (not bb) then ([],[],false) else
			let seqedge = IdtMap.find seqedgeid currgrrepr.edges
			in
			if seqedge.kind <> EOPSeqFlow then (ll1,ll2,bb) else
			let
			(eventnode,evog,evinc) = IdtMap.find seqedge.src currgrrepr.nodes
			in
			if eventnode.kind <> NOPEvent then ([],[],false) else
			if (RLMap.find "eventkind" eventnode.attrs) <> "throw" then ([],[],false) else
			if (RLMap.find "eventtype" eventnode.attrs) = "timer" then ((seqedge.src :: ll1), ll2, true) else if (RLMap.find "eventtype" eventnode.attrs) = othereventtype then (ll1, (seqedge.src :: ll2), true) else ([],[],false)
		) sndProcIncom ([],[],true)
		in
		if (not isgood) || ((List.length prevtimevents) <> 1) || ((List.length prevothevents) <> 1) then currgrrepr else
		let edgebeftimeid = grreprIncomingEdgeOfKind currgrrepr (List.hd prevtimevents) EOPSeqFlow
		and edgebefotherid = grreprIncomingEdgeOfKind currgrrepr (List.hd prevothevents) EOPSeqFlow
		in
		let edgebeftime = IdtMap.find edgebeftimeid currgrrepr.edges
		and edgebefother = IdtMap.find edgebefotherid currgrrepr.edges
		in
		if edgebeftime.src <> edgebefother.src then currgrrepr else
		let (prevGatewayN, prevGatewayOutg, prevGatewayIncom) = IdtMap.find edgebeftime.src currgrrepr.nodes
		in
		let edgetogatewayid = grreprIncomingEdgeOfKind currgrrepr prevGatewayN.id EOPSeqFlow
		in
		let edgetogateway = IdtMap.find edgetogatewayid currgrrepr.edges
		in
		let (taskBefGatewayN, taskBefGatewayOutg, taskBefGatewayIncom) = IdtMap.find edgetogateway.src currgrrepr.nodes
		in
		let (timerstatel, isgood) = IdtSet.fold (fun readedgeid (ll,bb) ->
			let readedge = IdtMap.find readedgeid currgrrepr.edges
			in
			if readedge.kind <> EOPRead then (ll,bb) else
			let (ts,tso,tsi) = IdtMap.find readedge.src currgrrepr.nodes
			in
			(((ts,tso,tsi) :: ll), true)
		) taskBefGatewayIncom ([],true)
		in
		if (not isgood) || ((List.length timerstatel) <> 1) then currgrrepr else
		let (timerStateN, timerStateOutg, timerStateIncom) = List.hd timerstatel
		in
		let (possfstprocid, boundarytype) =
			let currPosition = ref taskBefGatewayN.id
			and makestep = ref true
			and foundfirstproc = ref false
			and foundboundary = ref "plain"
			in
			while !makestep do
				let (cpnode, _, cpincom) = IdtMap.find !currPosition currgrrepr.nodes
				in
				if (cpnode.kind = NOPSubprocess) then
				begin
					foundfirstproc := true;
					makestep := false
				end
				else
				begin
					(if (cpnode.kind = NOPEvent) && ((RLMap.find "eventkind" cpnode.attrs) = "boundary") then
						foundboundary := RLMap.find "eventtype" cpnode.attrs );
					let outseqflow = IdtSet.fold (fun outedgeid ll ->
						let outedge = IdtMap.find outedgeid currgrrepr.edges
						in
						if (outedge.kind = EOPSeqFlow) || (outedge.kind = EOPBoundary) then outedge.src :: ll else ll
					) cpincom []
					in
					if ((List.length outseqflow) = 1) then
					begin
						currPosition := List.hd outseqflow
					end
					else
					begin
						makestep := false
					end
				end
			done;
			((if !foundfirstproc then Some !currPosition else None), !foundboundary)
		in
		if possfstprocid = None then currgrrepr else
		let Some fstProcId = possfstprocid
		in
		let (fstProcN, fstProcOutg, fstProcIncom) = IdtMap.find fstProcId currgrrepr.nodes
		in
		let possfstEndNode = IdtSet.fold (fun cntedgeid res ->
			match res with
			| Some _ -> res
			| None ->
				let cntedge = IdtMap.find cntedgeid currgrrepr.edges
				in
				if cntedge.kind <> EOPContain then res else
				let (pfn,pfog,pfin) = IdtMap.find cntedge.tgt currgrrepr.nodes
				in
				if (pfn.kind = NOPEvent) && ((RLMap.find "eventkind" pfn.attrs) = "end") && ((RLMap.find "eventtype" pfn.attrs) = boundarytype) then Some (pfn,pfog,pfin) else None
		) fstProcOutg None
		in
		if possfstEndNode = None then currgrrepr else
		let Some (fstEndNodeN, fstEndNodeOutg, fstEndNodeIncom) = possfstEndNode
		in
		let writingNodeId = (IdtMap.find (grreprIncomingEdgeOfKind currgrrepr fstEndNodeN.id EOPSeqFlow) currgrrepr.edges).src
		in
		let (writingNode,_,writingNodeIncom) = IdtMap.find writingNodeId currgrrepr.nodes
		in
		let possFreshStateId = IdtSet.fold (fun incedgeid res ->
			match res with
			| Some _ -> res
			| None ->
				let incedge = IdtMap.find incedgeid currgrrepr.edges
				in
				if incedge.kind <> EOPRead then res else Some incedge.src
		) writingNodeIncom None
		in
		if possFreshStateId = None then currgrrepr else
		let Some freshStateId = possFreshStateId
		in
		let edgeToParenProcId = grreprIncomingEdgeOfKind currgrrepr fstProcId EOPContain
		and (freshState,_,_) = IdtMap.find freshStateId currgrrepr.nodes
		in
		let parenProcId = (IdtMap.find edgeToParenProcId currgrrepr.edges).src
		in
		let activeProcessName = "Active_process_" ^ (NewName.to_string sndProcId)
		and stateDigestName = "State_digest_" ^ (NewName.to_string sndProcId)
		in
		let activeProcessDataset = {
			kind = NOPDataset;
			id = NewName.get ();
			attrs = RLMap.singleton "name" activeProcessName;
		}
		and stateDigestDataset = {
			kind = NOPDataset;
			id = NewName.get ();
			attrs = RLMap.singleton "name" stateDigestName;
		}
		in
		let activeProcessContainEdge = {
			kind = EOPContain;
			src = parenProcId;
			tgt = activeProcessDataset.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		and stateDigestContainEdge = {
			kind = EOPContain;
			src = parenProcId;
			tgt = stateDigestDataset.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		in
		let gr0 = grreprAddEdge (grreprAddEdge (grreprAddNode (grreprAddNode currgrrepr activeProcessDataset) stateDigestDataset) activeProcessContainEdge) stateDigestContainEdge
		in
		let gr1 = grreprRemoveNode (cutSequenceOverNode gr0 writingNodeId) writingNodeId
		in
		let activeProcessCheckerTask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "name" ("Check if there is active process for " ^ (NewName.to_string sndProcId)) (RLMap.singleton "sql" ("equals(" ^ activeProcessName ^ ".b,1)"));
		}
		in
		let activeProcessCheckerConnection = {
			kind = EOPRead;
			id = NewName.get ();
			src = activeProcessDataset.id;
			tgt = activeProcessCheckerTask.id;
			attrs = RLMap.empty;
		}
		in
		let gr2 = grreprAddEdge (grreprPutTaskToSeqFlow gr1 (grreprIncomingEdgeOfKind gr1 fstEndNodeN.id EOPSeqFlow) activeProcessCheckerTask) activeProcessCheckerConnection
		in
		let activeProcessCheckerGateway = {
			kind = NOPGateway;
			id = NewName.get ();
			attrs = RLMap.singleton "gatewaykind" "exclusive";
		}
		in
		let gr3 = grreprPutTaskToSeqFlow gr2 (grreprIncomingEdgeOfKind gr2 fstEndNodeN.id EOPSeqFlow) activeProcessCheckerGateway
		in
		let checkerGatewayOutedgeId = grreprIncomingEdgeOfKind gr3 fstEndNodeN.id EOPSeqFlow
		in
		let checkerGatewayOutedge = IdtMap.find checkerGatewayOutedgeId gr3.edges
		in
		let gr4 = {gr3 with edges = IdtMap.add checkerGatewayOutedgeId {checkerGatewayOutedge with attrs = RLMap.add "branch" "false" checkerGatewayOutedge.attrs} gr3.edges}
		in
		let activeProcessSetterTask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "name" ("Setter of " ^ activeProcessName) (RLMap.singleton "sql" (activeProcessName ^ ".b = 1"));
		}
		in
		let activeProcessSetterConnection = {
			kind = EOPWrite;
			id = NewName.get ();
			src = activeProcessSetterTask.id;
			tgt = activeProcessDataset.id;
			attrs = RLMap.empty;
		}
		in
		let gr5 = grreprAddEdge (grreprPutTaskToSeqFlow gr4 (grreprIncomingEdgeOfKind gr4 fstEndNodeN.id EOPSeqFlow) activeProcessSetterTask) activeProcessSetterConnection
		in
		let senderTask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.singleton "name" "Send";
		}
		in
		let senderTaskConn1 = {
			kind = EOPRead;
			src = freshStateId;
			tgt = senderTask.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		and senderTaskConn2 = {
			kind = EOPMsgFlow;
			src = senderTask.id;
			tgt = startNode.id;
			id = NewName.get ();
			attrs = RLMap.singleton "securechannel" "true";
		}
		in
		let gr6 = grreprAddEdge (grreprAddEdge (grreprPutTaskToSeqFlow gr5 (grreprIncomingEdgeOfKind gr5 fstEndNodeN.id EOPSeqFlow) senderTask) senderTaskConn1) senderTaskConn2
		in
		let activeProcessOverwriterTask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" (stateDigestName ^ " = " ^ (RLMap.find "name" freshState.attrs) ^ "\n" ^ (RLMap.find "name" timerStateN.attrs) ^ ".state = 1") (RLMap.singleton "name" "Copy state digest");
		}
		in
		let apOwConn1 = {
			kind = EOPSeqFlow;
			src = activeProcessCheckerGateway.id;
			tgt = activeProcessOverwriterTask.id;
			id = NewName.get ();
			attrs = RLMap.singleton "branch" "true";
		}
		and apOwConn2 = {
			kind = EOPRead;
			src = freshStateId;
			tgt = activeProcessOverwriterTask.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		and apOwConn3 = {
			kind = EOPWrite;
			src = activeProcessOverwriterTask.id;
			tgt = stateDigestDataset.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		and apOwConn4 = {
			kind = EOPContain;
			src = fstProcId;
			tgt = activeProcessOverwriterTask.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		and apOwConn5 = {
			kind = EOPWrite;
			src = activeProcessOverwriterTask.id;
			tgt = timerStateN.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		in
		let gr7 = grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddEdge (grreprAddNode gr6 activeProcessOverwriterTask) apOwConn1) apOwConn2) apOwConn3) apOwConn4) apOwConn5
		in
		let fstProcEndGateway = {
			kind = NOPGateway;
			id = NewName.get ();
			attrs = RLMap.singleton "gatewaykind" "exclusive"
		}
		in
		let fstProcEndGWIncEdge = {
			kind = EOPSeqFlow;
			src = activeProcessOverwriterTask.id;
			tgt = fstProcEndGateway.id;
			id = NewName.get ();
			attrs = RLMap.empty;
		}
		in
		let gr8 = grreprAddEdge (grreprPutTaskToSeqFlow gr7 (grreprIncomingEdgeOfKind gr7 fstEndNodeN.id EOPSeqFlow) fstProcEndGateway) fstProcEndGWIncEdge
		in
		let timerResetTask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" ((RLMap.find "name" timerStateN.attrs) ^ ".state = 0") (RLMap.singleton "name" "Timer state resetting task");
		}
		in
		let
		timerResettingEdge = {
			kind = EOPWrite;
			id = NewName.get ();
			src = timerResetTask.id;
			tgt = timerStateN.id;
			attrs = RLMap.empty;
		}
		in
		let gr9 = grreprAddEdge (grreprPutTaskToSeqFlow gr8 (grreprIncomingEdgeOfKind gr8 condGatewayNode.id EOPSeqFlow) timerResetTask) timerResettingEdge
		in
		let timerCheckingTask = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" ("equals(" ^ (RLMap.find "name" timerStateN.attrs) ^ ".state, 1)") (RLMap.singleton "name" "check timer status");
		}
		in
		let timerCheckConnection = {
			kind = EOPRead;
			id = NewName.get ();
			src = timerStateN.id;
			tgt = timerCheckingTask.id;
			attrs = RLMap.empty;
		}
		in
		let gr10 = grreprAddEdge (grreprPutTaskToSeqFlow gr9 (grreprIncomingEdgeOfKind gr9 condGatewayNode.id EOPSeqFlow) timerCheckingTask) timerCheckConnection
		in
		let gr11 = {gr10 with nodes = let (_ ,cgn1, cgn2) = IdtMap.find condGatewayNode.id gr10.nodes in IdtMap.add condGatewayNode.id ({condGatewayNode with
				attrs = RLMap.add "gatewaykind" "exclusive" condGatewayNode.attrs
			}, cgn1, cgn2) gr10.nodes }
		in
		let gr12 = {gr11 with edges = IdtMap.add edgebeftime.id {edgebeftime with attrs = RLMap.add "branch" "false" edgebeftime.attrs}
			(IdtMap.add edgebefother.id {edgebefother with attrs = RLMap.add "branch" "true" edgebefother.attrs} gr11.edges)
		}
		in
		let noMoreActiveProcess = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" (activeProcessName ^ ".b = 0") (RLMap.singleton "name" "reset Active Process");
		}
		in
		let noMoreActiveProcessConn = {
			kind = EOPWrite;
			id = NewName.get ();
			src = noMoreActiveProcess.id;
			tgt = activeProcessDataset.id;
			attrs = RLMap.empty;
		}
		in
		let gr13 = grreprAddEdge (grreprPutTaskToSeqFlow gr12 (grreprIncomingEdgeOfKind gr12 timerEvNode.id EOPSeqFlow) noMoreActiveProcess) noMoreActiveProcessConn
		in
		let (sndProcStateDig, _, _) = IdtMap.find evWrittenStateId gr13.nodes
		in
		let stateDigestCopier = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" ((RLMap.find "name" sndProcStateDig.attrs) ^ " = " ^ stateDigestName) (RLMap.singleton "name" "copy state digest")
		}
		in
		let stateDigestCopierConn1 = {
			kind = EOPRead;
			id = NewName.get ();
			src = stateDigestDataset.id;
			tgt = stateDigestCopier.id;
			attrs = RLMap.empty;
		}
		and stateDigestCopierConn2 = {
			kind = EOPWrite;
			id = NewName.get ();
			src = stateDigestCopier.id;
			tgt = evWrittenStateId;
			attrs = RLMap.empty;
		}
		in
		let gr14 = grreprAddEdge (grreprAddEdge (grreprPutTaskToSeqFlow gr13 (grreprIncomingEdgeOfKind gr13 otherEvNode.id EOPSeqFlow) stateDigestCopier) stateDigestCopierConn1) stateDigestCopierConn2
		in
		let activeProcResetPr2 = {
			kind = NOPTask;
			id = NewName.get ();
			attrs = RLMap.add "sql" (activeProcessName ^ ".b = 0") (RLMap.singleton "name" "reset active process flag");
		}
		in
		let activeProcessResetPr2Conn = {
			kind = EOPWrite;
			id = NewName.get ();
			src = activeProcResetPr2.id;
			tgt = activeProcessDataset.id;
			attrs = RLMap.empty;
		}
		in
		let gr15 = grreprAddEdge (grreprPutTaskToSeqFlow gr14 (grreprIncomingEdgeOfKind gr14 otherEvNode.id EOPSeqFlow) activeProcResetPr2) activeProcessResetPr2Conn
		in
		let gr16 = grreprRemoveNode (grreprRemoveNode (cutSequenceOverNode (cutSequenceOverNode gr15 timerEvNode.id) otherEvNode.id) timerEvNode.id) otherEvNode.id
		in
		let (sndProcN, sndProcOutg, sndProcIncom) = IdtMap.find sndProcId gr16.nodes
		and (fstProcN, fstProcOutg, fstProcIncom) = IdtMap.find fstProcId gr16.nodes
		in
		let gr17 = IdtSet.fold (fun edgeid gr' ->
			let edge = IdtMap.find edgeid gr'.edges
			in
			if edge.kind = EOPSeqFlow then grreprRemoveEdge gr' edgeid else gr'
		) (IdtSet.union sndProcIncom fstProcOutg) gr16
		in
		let newParalG = {
			kind = NOPGateway;
			id = NewName.get ();
			attrs = RLMap.singleton "gatewaykind" "parallel";
		}
		in
		let paralGTo2ndProc = {
			kind = EOPSeqFlow;
			id = NewName.get ();
			src = newParalG.id;
			tgt = sndProcId;
			attrs = RLMap.empty
		}
		in
		grreprAddEdge (grreprPutTaskToSeqFlow gr17 (grreprIncomingEdgeOfKind gr17 fstProcId EOPSeqFlow) newParalG) paralGTo2ndProc
	) grrepr.nodes grrepr
;;

let readABEAttributeSetFromTaskAttrs attrs =
	let n = int_of_string (RLMap.find "abAttrNum" attrs)
	in
	List.fold_right (fun idx s -> RLSet.add (RLMap.find ("Attribute_" ^ (string_of_int idx)) attrs) s) (intfromto 0 (n-1)) RLSet.empty
;;

let (readDataDeclarations : graphgraphtype -> (string -> NewName.idtype) -> datasetdeclaration RLMap.t * componentdefinition list IdtMap.t * definingexpr IdtMap.t * graphgraphtype ) = fun grrepr idForStr ->
	let (taskcomps, guards, addedIVs) = IdtMap.fold (fun nodeid ((node : nodeonpicturetype),noutg,nincom) (tccurr,gcurr, addivll) ->
		if RLMap.mem "sql" node.attrs then
		begin
			let isGuard =
				try
					let ogedgeid = grreprOutgoingEdgeOfKind grrepr nodeid EOPSeqFlow
					in
					let ogedge = IdtMap.find ogedgeid grrepr.edges
					in
					let (nextnode,_,nnincom) = IdtMap.find ogedge.tgt grrepr.nodes
					in
					(nextnode.kind = NOPGateway) && ((RLMap.find "gatewaykind" nextnode.attrs) = "exclusive") && (
						(IdtSet.fold (fun inedgeid nn ->
							let inedge = IdtMap.find inedgeid grrepr.edges
							in
							if inedge.kind = EOPSeqFlow then nn+1 else nn
						) nnincom 0) = 1)
				with _ -> false
			in
			match (translateTaskScript (RLMap.find "sql" node.attrs) isGuard) with
			| Left deflist -> ((IdtMap.add nodeid deflist tccurr), gcurr, addivll)
			| Right gexpr -> (tccurr, (IdtMap.add nodeid gexpr gcurr), addivll)
		end
		else if (RLMap.mem "skencrypt" node.attrs) || (RLMap.mem "skdecrypt" node.attrs) || (RLMap.mem "abdecrypt" node.attrs) || (RLMap.mem "pkdecrypt" node.attrs) then
		begin
			let isEnc = RLMap.mem "skencrypt" node.attrs
			and isAB = RLMap.mem "abdecrypt" node.attrs
			and ispkdec = RLMap.mem "pkdecrypt" node.attrs
			in
			let outDatasetName =
				let ogedgeid = grreprOutgoingEdgeOfKind grrepr nodeid EOPWrite
				in
				let ogedge = IdtMap.find ogedgeid grrepr.edges
				in
				let (nextnode,_,_) = IdtMap.find ogedge.tgt grrepr.nodes
				in
				RLMap.find "name" nextnode.attrs
			in
			let keyname = RLMap.find (if isAB then "abdeckey" else if ispkdec then "pkdeckey" else "skkey") node.attrs
			and textname = RLMap.find (if isAB then "abciphertext" else if ispkdec then "pkciphertext" else "sktext") node.attrs
			in
			let encargs = (if isEnc then [DEVar ("IV_for_" ^ (NewName.to_string nodeid), "iv")] else []) @ [DEVar (keyname, "key"); DEVar (textname, "data")]
			in
			let deflist = [((outDatasetName, if isAB then "key" else "data"), DEOp ((if isAB then OPABDecrypt else if ispkdec then OPPKDecrypt else if isEnc then OPEncrypt else OPDecrypt), encargs)); ((outDatasetName, "*\\data"), DEVar (textname,"*\\data"))]
			in
			((IdtMap.add nodeid deflist tccurr), gcurr, (if isEnc then nodeid :: addivll else addivll))
		end
		else if (RLMap.mem "abencrypt" node.attrs) then
		begin
			let outDatasetName =
				let ogedgeid = grreprOutgoingEdgeOfKind grrepr nodeid EOPWrite
				in
				let ogedge = IdtMap.find ogedgeid grrepr.edges
				in
				let (nextnode,_,_) = IdtMap.find ogedge.tgt grrepr.nodes
				in
				RLMap.find "name" nextnode.attrs
			in
			let keyname = RLMap.find "abenckey" node.attrs
			and textname = RLMap.find "abplaintext" node.attrs
			and attrset = readABEAttributeSetFromTaskAttrs node.attrs
			in
			let encargs = [DEVar ("IV_for_" ^ (NewName.to_string nodeid), "iv"); DEVar (keyname, "key"); DEVar (textname, "key")]
			in
			let deflist = [((outDatasetName, "data"), DEOp ((OPABEncrypt attrset), encargs)) ; ((outDatasetName, "*\\key"), DEVar (textname,"*\\key"))]
			in
			((IdtMap.add nodeid deflist tccurr), gcurr, (nodeid :: addivll))
		end
		else if (RLMap.mem "pkencrypt" node.attrs) then
		begin
			let outDatasetName =
				let ogedgeid = grreprOutgoingEdgeOfKind grrepr nodeid EOPWrite
				in
				let ogedge = IdtMap.find ogedgeid grrepr.edges
				in
				let (nextnode,_,_) = IdtMap.find ogedge.tgt grrepr.nodes
				in
				RLMap.find "name" nextnode.attrs
			in
			let keyname = RLMap.find "pkenckey" node.attrs
			and textname = RLMap.find "pkplaintext" node.attrs
			in
			let encargs = [DEVar ("IV_for_" ^ (NewName.to_string nodeid), "iv"); DEVar (keyname, "key"); DEVar (textname, "data")]
			in
			let deflist = [((outDatasetName, "data"), DEOp (OPPKEncrypt, encargs)) ; ((outDatasetName, "*\\key"), DEVar (textname,"*\\data"))]
			in
			((IdtMap.add nodeid deflist tccurr), gcurr, (nodeid :: addivll))
		end
		else
		begin
			let possOutMsgFlow = IdtSet.fold (fun outedgeid res ->
				match res with
				| Some _ -> res
				| None ->
					let outedge = IdtMap.find outedgeid grrepr.edges
					in
					if outedge.kind <> EOPMsgFlow then None else Some outedge
			) noutg None
			in
			if possOutMsgFlow = None then (tccurr, gcurr, addivll) else
			let possIncomingDataset = IdtSet.fold (fun incedgeid res ->
				match res with
				| Some _ -> res
				| None ->
					let incedge = IdtMap.find incedgeid grrepr.edges
					in
					if incedge.kind <> EOPRead then None else Some incedge
			) nincom None
			in
			if possIncomingDataset = None then (tccurr, gcurr, addivll) else
			let Some outMsgFlow = possOutMsgFlow
			in
			let (recvnode, recvoutg, _) = IdtMap.find outMsgFlow.tgt grrepr.nodes
			in
			let possStoreDataset = IdtSet.fold (fun outedgeid res ->
				match res with
				| Some _ -> res
				| None ->
					let outedge = IdtMap.find outedgeid grrepr.edges
					in
					if outedge.kind <> EOPWrite then None else Some outedge
			) recvoutg None
			in
			if possStoreDataset = None then (tccurr, gcurr, addivll) else
			let Some incomingDataset = possIncomingDataset
			and Some storeDataset = possStoreDataset
			in
			let (incomingDSnode,_,_) = IdtMap.find incomingDataset.src grrepr.nodes
			and (storeDSnode,_,_) = IdtMap.find storeDataset.tgt grrepr.nodes
			in
			let tccurr' = IdtMap.add nodeid [((RLMap.find "name" storeDSnode.attrs, "*"), DEVar (RLMap.find "name" incomingDSnode.attrs, "*"))] tccurr
			in (tccurr', gcurr, addivll)
		end
	) grrepr.nodes (IdtMap.empty, IdtMap.empty, [])
	in
	let rec addExprComps dsds dexpr =
		match dexpr with
		| DEVar (rhsds, rhscomp) ->
			let (_,dsdecl) = (try RLMap.find rhsds dsds with Not_found -> (rhsds, RLMap.empty))
			in
			RLMap.add rhsds (rhsds, (RLMap.add rhscomp VAny dsdecl)) dsds
		| DEAppl (_, dexprl)
		| DEOp (_, dexprl) ->
			List.fold_right (fun dexpr' dsdscurr -> addExprComps dsdscurr dexpr') dexprl dsds
		| _ -> dsds
	in
	let (dsd0, dsdincl) = IdtMap.fold (fun _ compdefll (dsdcurr, inclcurr) ->
		List.fold_right (fun ((lhsds, lhscomp), rhsexpr) (dsdcxx, inclcxx) ->
			if lhscomp = "*" then
			begin
				let DEVar (rhsds,_) = rhsexpr
				in
				let incset = try RLMap.find rhsds inclcxx with Not_found -> RLSet.empty
				in
				let inclcxx' = RLMap.add rhsds (RLSet.add lhsds incset) inclcxx
				in
				(dsdcxx, inclcxx')
			end else
			if lhscomp = "*\\data" then
			begin
				let DEVar (rhsds,_) = rhsexpr
				in
				let incset = try RLMap.find rhsds inclcxx with Not_found -> RLSet.empty
				in
				let inclcxx' = RLMap.add rhsds (RLSet.add lhsds incset) inclcxx
				in
				(dsdcxx, inclcxx')
			end else
			if lhscomp = "*\\key" then
			begin
				let DEVar (rhsds,_) = rhsexpr
				in
				let incset = try RLMap.find rhsds inclcxx with Not_found -> RLSet.empty
				in
				let inclcxx' = RLMap.add rhsds (RLSet.add lhsds incset) inclcxx
				in
				(dsdcxx, inclcxx')
			end else
			begin
				let (_,dsdecl) = try RLMap.find lhsds dsdcxx with Not_found -> (lhsds, RLMap.empty)
				in
				let dsdecl' = RLMap.add lhscomp VAny dsdecl
				in
				let dsdcxx' = RLMap.add lhsds (lhsds, dsdecl') dsdcxx
				in
				let dsdcxx'' = addExprComps dsdcxx' rhsexpr
				in
				(dsdcxx'', inclcxx)
			end
		) compdefll (dsdcurr, inclcurr)
	) taskcomps (RLMap.empty, RLMap.empty)
	in
	let dsd1 = IdtMap.fold (fun _ gexpr dsdcurr ->
		addExprComps dsdcurr gexpr
	) guards dsd0
	in
	let changed = ref true
	and dsdr = ref dsd1
	in
	while !changed do
		changed := false;
		let combiner _ lhopt rhopt = match lhopt,rhopt with
			| None, None -> None
			| None, Some x -> (changed := true; Some x)
			| Some x, None -> Some x
			| Some x, Some y -> Some x
		in
		RLMap.iter (fun rhsds lhsdss ->
			RLSet.iter (fun lhsds ->
				let rhsdecls = try snd (RLMap.find rhsds !dsdr) with Not_found -> RLMap.empty
				and lhsdecls = try snd (RLMap.find lhsds !dsdr) with Not_found -> RLMap.empty
				in
				dsdr := RLMap.add lhsds (lhsds, (RLMap.merge combiner lhsdecls rhsdecls)) !dsdr
			) lhsdss
		) dsdincl
	done;
	let updtaskcomps = IdtMap.fold (fun taskid cdefl updtccurr ->
		let updcdefl = List.fold_right (fun (((lhsds, lhscomp), rhside) as cdef) currll ->
			if lhscomp = "*" then
			begin
				let DEVar (rhsds,_) = rhside
				in
				let rhsdesc = snd (RLMap.find rhsds !dsdr)
				in
				RLMap.fold (fun compname _ ll' ->
					((lhsds, compname), DEVar (rhsds, compname)) :: ll'
				) rhsdesc currll
			end
			else if lhscomp = "*\\data" then
			begin
				let DEVar (rhsds,_) = rhside
				in
				let rhsdesc = snd (RLMap.find rhsds !dsdr)
				in
				RLMap.fold (fun compname _ ll' ->
					if compname = "data" then ll' else
					((lhsds, compname), DEVar (rhsds, compname)) :: ll'
				) rhsdesc currll
			end
			else if lhscomp = "*\\key" then
			begin
				let DEVar (rhsds,_) = rhside
				in
				let rhsdesc = snd (RLMap.find rhsds !dsdr)
				in
				RLMap.fold (fun compname _ ll' ->
					if compname = "key" then ll' else
					((lhsds, compname), DEVar (rhsds, compname)) :: ll'
				) rhsdesc currll
			end
			else cdef :: currll
		) cdefl []
		in IdtMap.add taskid updcdefl updtccurr
	) taskcomps IdtMap.empty
	in
	let grrepr' = List.fold_right (fun encnodeid grcurr ->
		let (encnode,_,_) = IdtMap.find encnodeid grcurr.nodes
		in
		let containedgeid = grreprIncomingEdgeOfKind grcurr encnodeid EOPContain
		in
		let containedge = IdtMap.find containedgeid grcurr.edges
		in
		let newdataset = {
			kind = NOPDataset;
			id = NewName.get ();
			attrs = RLMap.singleton "name" ("IV_for_" ^ (NewName.to_string encnodeid))
		}
		in
		let newContainEdge = {
			kind = EOPContain;
			id = NewName.get ();
			src = containedge.src;
			tgt = newdataset.id;
			attrs = RLMap.empty;
		}
		and newReadEdge = {
			kind = EOPRead;
			id = NewName.get ();
			src = newdataset.id;
			tgt = encnodeid;
			attrs = RLMap.empty;
		}
		in
		grreprAddEdge (grreprAddEdge (grreprAddNode grcurr newdataset) newContainEdge) newReadEdge
	) addedIVs grrepr
	in
	(!dsdr, updtaskcomps, guards, grrepr')
;;

let foldGraphNodesByControlFlow (f : NewName.idtype -> nodeonpicturetype * IdtSet.t * IdtSet.t -> 'a IdtMap.t list -> 'a ) grrepr =
	let outerProcesses = IdtMap.fold (fun nodeid ((node : nodeonpicturetype), noutg, nincom) ss ->
		if (node.kind = NOPSubprocess) && (IdtSet.is_empty nincom) then IdtSet.add nodeid ss else ss
	) grrepr.nodes IdtSet.empty
	in
	let curracc = ref IdtMap.empty
	in
	let rec processProcess procid louter =
		let nq = Queue.create ()
		and handledNodes = ref IdtSet.empty
		in
		List.iter (fun startnodeid ->
			Queue.add startnodeid nq;
			handledNodes := IdtSet.add startnodeid !handledNodes
		) (findProcessStartNodes grrepr procid);
		while (not (Queue.is_empty nq)) do
			let currNodeId = Queue.take nq
			in
			let (currNode, currOutg, currIncom) = IdtMap.find currNodeId grrepr.nodes
			in
			if IdtSet.for_all (fun inedgeid ->
				let inedge = IdtMap.find inedgeid grrepr.edges
				in
				(inedge.kind <> EOPSeqFlow) || (IdtMap.mem inedge.src !curracc)
			) currIncom then
			begin
				let mkFstInp = IdtSet.fold (fun inedgeid res ->
					let inedge = IdtMap.find inedgeid grrepr.edges
					in
					if inedge.kind = EOPSeqFlow then IdtMap.add inedge.src (IdtMap.find inedge.src !curracc) res else res
				) currIncom IdtMap.empty
				in
				(if currNode.kind = NOPSubprocess then processProcess currNodeId (mkFstInp :: louter) else
					curracc := IdtMap.add currNodeId (f currNodeId (currNode, currOutg, currIncom) (mkFstInp :: louter)) !curracc);
				IdtSet.iter (fun nextEdgeId ->
					let nextEdge = IdtMap.find nextEdgeId grrepr.edges
					in
					if (nextEdge.kind = EOPSeqFlow) && (not (IdtSet.mem nextEdge.tgt !handledNodes)) then
					begin
						Queue.add nextEdge.tgt nq;
						handledNodes := IdtSet.add nextEdge.tgt !handledNodes
					end else ()
				) currOutg
			end
			else Queue.add currNodeId nq
		done
	in
	IdtSet.iter (fun prid -> processProcess prid []) outerProcesses;
	!curracc
;;

let ((findMsgFlowProcPaths, introduceProcPointers) : ((graphgraphtype -> NewName.idtype option list list IdtMap.t) * (graphgraphtype -> NewName.idtype option list list IdtMap.t -> IdtSet.t IdtMap.t) )) =
	let rec pathToContainingProc grrepr nodeid =
		let (node, noutg, nincom) = IdtMap.find nodeid grrepr.nodes
		in
		let possincontain = IdtSet.fold (fun inedgeid res ->
			match res with
			| Some _ -> res
			| None ->
				let inedge = IdtMap.find inedgeid grrepr.edges
				in
				if inedge.kind = EOPContain then Some inedge else None
		) nincom None
		in
		match possincontain with
		| None -> []
		| Some inedge ->
			let outernodeid = inedge.src
			in
			outernodeid :: (pathToContainingProc grrepr outernodeid)
	in
	let rec absToRelPath pathToSrc pathToTgt = match pathToSrc with
		| [] -> List.map (fun x -> Some x) pathToTgt
		| x :: xs -> (match pathToTgt with
			| [] -> List.map (fun _ -> None) pathToSrc
			| y :: ys -> if x = y then absToRelPath xs ys else
					List.append (List.map (fun x -> None) pathToSrc) (List.map (fun x -> Some x) pathToTgt)
		)
	in
	let f1 = fun grrepr ->
	IdtMap.fold (fun nodeid ((node : nodeonpicturetype), noutg, nincom) currres ->
		if (node.kind = NOPEvent) && (let ek = (RLMap.find "eventkind" node.attrs) in (ek = "catch") || (ek = "start")) && ((RLMap.find "eventtype" node.attrs) = "message") then
		begin
			let eventnodepath = List.rev (pathToContainingProc grrepr nodeid)
			in
			let incomingpaths = IdtSet.fold (fun edgeid ll ->
				let edge = IdtMap.find edgeid grrepr.edges
				in
				if edge.kind <> EOPMsgFlow then ll
				else
				let sendnodepath = List.rev (pathToContainingProc grrepr edge.src)
				in
				(absToRelPath eventnodepath sendnodepath) :: ll
			) nincom []
			in
			IdtMap.add nodeid incomingpaths currres
		end
		else
		begin
			let sendnodepath = lazy (List.rev (pathToContainingProc grrepr nodeid))
			in
			let outgoingpaths = IdtSet.fold (fun edgeid ll ->
				let edge = IdtMap.find edgeid grrepr.edges
				in
				if edge.kind <> EOPMsgFlow then ll
				else
				let (tgtnode,_,_) = IdtMap.find edge.tgt grrepr.nodes
				in
				if (tgtnode.kind <> NOPEvent) || ((RLMap.find "eventkind" tgtnode.attrs) <> "start") then ll
				else
				let recvnodepath = List.rev (pathToContainingProc grrepr edge.tgt)
				in
				(absToRelPath (Lazy.force sendnodepath) recvnodepath) :: ll
			) noutg []
			in
			if outgoingpaths <> [] then IdtMap.add nodeid outgoingpaths currres else currres
		end
	) grrepr.nodes IdtMap.empty
	and f2 = fun grrepr msgflowpaths ->
		let isSendNodeStartingAProcess node noutg =
			IdtSet.exists (fun outedgeid ->
				let outedge = IdtMap.find outedgeid grrepr.edges
				in
				if outedge.kind <> EOPMsgFlow then false else
				let (tgtnode,_,_) = IdtMap.find outedge.tgt grrepr.nodes
				in
				(tgtnode.kind = NOPEvent) && ((RLMap.find "eventkind" tgtnode.attrs) = "start")
			) noutg
		in
		let leftMerger _ x y = match x, y with
			| None, None -> None
			| Some xx, _ -> Some xx
			| None, Some yy -> Some yy
		in
		let rightMerger k x y = leftMerger k y x
		in
		let (foldingFunction : NewName.idtype -> nodeonpicturetype * IdtSet.t * IdtSet.t -> ((NewName.idtype option list list IdtMap.t) * ((IdtSet.t * bool) option)) IdtMap.t list -> (NewName.idtype option list list IdtMap.t) * ((IdtSet.t * bool) option) ) = fun nodeid (node, noutg, nincom) availProcPtrList ->
			let flowInsCalculator procs = IdtMap.fold (fun _ availAtInc allAvail ->
				IdtMap.merge leftMerger availAtInc allAvail
			) procs IdtMap.empty
			in
			let flowIns = flowInsCalculator (IdtMap.map fst (List.hd availProcPtrList))
			in
			if ((node.kind = NOPEvent) && ((RLMap.find "eventkind" node.attrs) = "start") && ((RLMap.find "eventtype" node.attrs) = "message")) || (isSendNodeStartingAProcess node noutg) then
				let ppl = IdtMap.find nodeid msgflowpaths
				in
				let newpptr = NewName.get ()
				in
				((IdtMap.add newpptr ppl flowIns), Some (IdtSet.singleton newpptr, true))
			else if (node.kind = NOPEvent) && ((RLMap.find "eventkind" node.attrs) = "catch") && ((RLMap.find "eventtype" node.attrs) = "message") then
			begin
				let procPtrsOnHier = List.map (fun x -> flowInsCalculator (IdtMap.map fst x)) availProcPtrList
				in
				let rec procPtrsAccum currentColl useNones leftOvers = match leftOvers with
					| [] -> currentColl
					| thisOver :: nextOvers ->
						let thisOver' = IdtMap.map (fun prnamelistlist ->
							List.map (fun prnamelist -> List.append useNones prnamelist) prnamelistlist
						) thisOver
						in
						procPtrsAccum (IdtMap.merge leftMerger currentColl thisOver') (None :: useNones) nextOvers
				in
				let availPtrs = procPtrsAccum IdtMap.empty [] procPtrsOnHier
				in
				let recvnodepath = List.rev (pathToContainingProc grrepr nodeid)
				in
				let sendnodepaths = IdtSet.fold (fun incedgeid lll ->
					let incedge = IdtMap.find incedgeid grrepr.edges
					in
					if incedge.kind <> EOPMsgFlow then lll
					else
					(absToRelPath recvnodepath (List.rev (pathToContainingProc grrepr incedge.src))) :: lll
				) nincom []
				in
				let goodPtrs = IdtMap.filter (fun _ pathsInPtr ->
					List.for_all (fun sendnodepath ->
						List.mem sendnodepath pathsInPtr
					) sendnodepaths
				) availPtrs
				in
				let goodProcPtr = IdtMap.fold (fun ptr _ s -> IdtSet.add ptr s) goodPtrs IdtSet.empty
				(* let (goodProcPtr,_) = IdtMap.choose goodPtrs *)
				in
				(flowIns, Some (goodProcPtr, false))
			end
			else (flowIns, None)
		in
		let resWithSrc = foldGraphNodesByControlFlow foldingFunction grrepr
		in
		IdtMap.map (fun (_, Some (ptr,_)) -> ptr
		) (IdtMap.filter ( fun _ (_,x) -> match x with None -> false | Some _ -> true
		) resWithSrc)
	in (f1,f2)
;;

let (manyTimesUpdatedDatasets : graphgraphtype -> IdtSet.t * IdtSet.t * IdtSet.t) = fun grrepr ->
	IdtMap.fold (fun nodeid ((node : nodeonpicturetype),noutg,nincom) (ssmany, ss0, sspublish) ->
		if node.kind <> NOPDataset then (ssmany, ss0, sspublish)
		else
		let writecount = IdtSet.fold (fun edgeid cnt ->
			let edge = IdtMap.find edgeid grrepr.edges
			in
			if edge.kind = EOPWrite then cnt + 1 else cnt
		) nincom 0
		and readcount = IdtSet.fold (fun edgeid cnt ->
			let edge = IdtMap.find edgeid grrepr.edges
			in
			if edge.kind = EOPRead then cnt + 1 else cnt
		) noutg 0
		in
		((if writecount > 1 then IdtSet.add nodeid ssmany else ssmany), (if writecount = 0 then IdtSet.add nodeid ss0 else ss0), (if readcount = 0 then IdtSet.add nodeid sspublish else sspublish))
	) grrepr.nodes (IdtSet.empty, IdtSet.empty, IdtSet.empty)
;;

let (insecurelySentDatasets : graphgraphtype -> IdtSet.t) = fun grrepr ->
	IdtMap.fold (fun nodeid ((node : nodeonpicturetype),noutg,nincom) res ->
		if node.kind <> NOPTask then res else
		let incdatasetids = IdtSet.fold (fun dedgeid ss ->
			let dedge = IdtMap.find dedgeid grrepr.edges
			in
			if dedge.kind <> EOPRead then ss else IdtSet.add dedge.src ss
		) nincom IdtSet.empty
		in
		if IdtSet.exists (fun edgeid ->
			let cedge = IdtMap.find edgeid grrepr.edges
			in
			if cedge.kind <> EOPMsgFlow then false
			else
			((RLMap.find "securechannel" cedge.attrs) = "false")
		) noutg then IdtSet.union incdatasetids res else res
	) grrepr.nodes IdtSet.empty
;;

module type GiveType = sig
	type t
end;;

module ExtArray (T : GiveType) =
(struct
	type t = {
		content : T.t array ref;
		usedLen : int ref
	}
	
	let create () =	{content = ref [||]; usedLen = ref 0;}

	let getLen r = !(r.usedLen)
	
	let getArray r = Array.init !(r.usedLen) (fun i -> (!(r.content)).(i))
	
	let getV r idx = if (idx < 0) || (idx >= !(r.usedLen)) then raise (Invalid_argument "index is out of bounds") else (!(r.content)).(idx)
	
	let setV r idx v = if (idx < 0) || (idx >= !(r.usedLen)) then raise (Invalid_argument "index is out of bounds") else (!(r.content)).(idx) <- v
	
	let appendV r v =
		let l = Array.length (!(r.content))
		and u = !(r.usedLen)
		in
		r.usedLen := u+1;
		if u < l then
		begin
			setV r u v
		end
		else
		begin
			r.content := Array.init (if l = 0 then 1 else 2 * l) (fun i -> if i < l then (!(r.content)).(i) else v)
		end
end : sig
	type t
	val create : unit -> t
	val getLen : t -> int
	val getArray : t -> T.t array
	val getV : t -> int -> T.t
	val setV : t -> int -> T.t -> unit
	val appendV : t -> T.t -> unit
end);;

module GT_StoppingProc = struct type t = stoppingproc end;;
module GT_SprNetworkNode = struct type t = sprNetworkNode end;;
module EASP = ExtArray(GT_StoppingProc);;
module EASNN = ExtArray(GT_SprNetworkNode);;

let rec (makeProcStartingFromNode : graphgraphtype -> datasetdeclaration RLMap.t * componentdefinition list IdtMap.t * definingexpr IdtMap.t -> NewName.idtype option list list IdtMap.t -> IdtSet.t IdtMap.t -> IdtSet.t -> RLSet.t -> NewName.idtype -> (stoppingproc * NewName.idtype * NewName.idtype, anyproc) either) = fun grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets startNodeId ->
	let isOpeningGateway (node, noutg, nincom) =
		let c = IdtSet.fold (fun edgeid cnt ->
			let edge = IdtMap.find edgeid grrepr.edges
			in
			if edge.kind = EOPSeqFlow then cnt + 1 else cnt
		) nincom 0
		in
		(c <= 1)
	in
	let (startnode, startnOutg, startnIncom) = IdtMap.find startNodeId grrepr.nodes
	in
	if (startnode.kind = NOPGateway) && ((RLMap.find "gatewaykind" startnode.attrs) = "parallel") && (isOpeningGateway (startnode, startnOutg, startnIncom)) then
	begin
		let followings = IdtSet.fold (fun edgeid ll ->
			let edge = IdtMap.find edgeid grrepr.edges
			in
			if edge.kind = EOPSeqFlow then
				(makeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets edge.tgt) :: ll
			else ll
		) startnOutg []
		in
		if followings = [] then Right (PRStop SPRNil)
		else
		match (List.hd followings) with
			| Left (_, nxtnodeid, _) ->
				let prlist = List.map (fun (Left (apr, anodeid, _)) -> if nxtnodeid = anodeid then apr else raise (Failure "different follow-up nodes")) followings
				in
				let oedgeid = grreprOutgoingEdgeOfKind grrepr nxtnodeid EOPSeqFlow
				in
				let oedge = IdtMap.find oedgeid grrepr.edges
				in
				Left ((SPRParal prlist), oedge.tgt, oedgeid)
			| Right _ -> Right (PRParal (List.map (fun (Right x) -> x) followings))
	end
	else if startnode.kind = NOPSubprocess then
	begin
		let starteventid = List.hd (findProcessStartNodes grrepr startNodeId)
		in
		let prres = iterMakeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets starteventid
		in
(*		if RLMap.mem "repeat" startnode.attrs then *) (* At this point, every process should be replicated *)
			Right (PRReplicate (prres, RLMap.find "name" startnode.attrs))
(*		else Right prres *)
	end
	else if (startnode.kind = NOPEvent) && ((RLMap.find "eventkind" startnode.attrs) = "start") then
	begin
		let outedgeid = grreprOutgoingEdgeOfKind grrepr startNodeId EOPSeqFlow
		in
		let outedge = IdtMap.find outedgeid grrepr.edges
		in
		let inccontedgeid = grreprIncomingEdgeOfKind grrepr startNodeId EOPContain
		in
		let inccontedge = IdtMap.find inccontedgeid grrepr.edges
		in
		let (encproc,_,_) = IdtMap.find inccontedge.src grrepr.nodes
		in
		let encprocname = RLMap.find "name" encproc.attrs
		in
		let starttask = SPRTask (StartEvent ((try Some (IdtSet.choose (IdtMap.find startNodeId procpointers)) with Not_found -> None), encprocname))
		in
		let startAndRecv = if (RLMap.find "eventtype" startnode.attrs) = "message" then
			SPRSeq (starttask, (collectReceivings grrepr (startnode, startnOutg, startnIncom) procpointers dsdecls updDatasets))
			else starttask
		in
		Right (PRSeq (startAndRecv, (iterMakeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets outedge.tgt)))
	end
	else if (startnode.kind = NOPEvent) && ((RLMap.find "eventkind" startnode.attrs) = "end") then
	begin
		Right (PRStop SPRNil)
	end
	else if startnode.kind = NOPDataset then raise (Failure "trying to convert a dataset at startfromnode")
	else
	let (nwprocs, nwnodes, contProcs) = addToNetworkFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets startNodeId (* ([||], [||]) IdtMap.empty *)
	in
	match contProcs with
		| Left []
		| Right None -> Right (PRNetwork (nwprocs, nwnodes, []))
		| Left xs -> Right (PRNetwork (nwprocs, nwnodes, xs))
		| Right (Some (nid, eid)) -> Left (SPRNetwork (nwprocs, nwnodes), nid, eid)
and (collectReceivings : graphgraphtype -> nodeonpicturetype * IdtSet.t * IdtSet.t -> IdtSet.t IdtMap.t -> datasetdeclaration RLMap.t -> IdtSet.t -> stoppingproc) = fun grrepr (startNode, startnOutg, startnIncom) procpointers dsdecls updDatasets ->
	let receivings = IdtSet.fold (fun incedgeid ll ->
		let incedge = IdtMap.find incedgeid grrepr.edges
		in
		if incedge.kind <> EOPMsgFlow then ll else
		let sendPrPtr = if isProcessStartNode grrepr startNode.id then IdtSet.choose (IdtMap.find incedge.src procpointers) else NewName.invalid_id
		in
		let (sendNode, _, sendNIncom) = IdtMap.find incedge.src grrepr.nodes
		in
		let Some dataNode = IdtSet.fold (fun dataEdgeId res ->
			match res with
				| Some _ -> res
				| None ->
					let dataEdge = IdtMap.find dataEdgeId grrepr.edges
					in
					if dataEdge.kind <> EOPRead then None else
					let ((dn : nodeonpicturetype),_,_) = IdtMap.find dataEdge.src grrepr.nodes
					in
					Some dn
		) sendNIncom None
		in
		(incedge, sendPrPtr, dataNode) :: ll
	) startnIncom []
	in
	print_string "Collecting receivings for node no. ";
	print_endline (NewName.to_string startNode.id);
	List.iter (fun (incedge, sendprptr, (datanode : nodeonpicturetype)) ->
		print_string ("Over edge " ^ (NewName.to_string incedge.id) ^ " comes datanode no. " ^ (NewName.to_string datanode.id) ^ " from process no. " ^ (NewName.to_string sendprptr) ^ "\n")
	) receivings;
	
	let Some storePlace = IdtSet.fold (fun dataEdgeId res ->
		match res with
			| Some _ -> res
			| None ->
				let dataEdge = IdtMap.find dataEdgeId grrepr.edges
				in
				if dataEdge.kind <> EOPWrite then None else
				let (dn,_,_) = IdtMap.find dataEdge.tgt grrepr.nodes
				in
				Some dn
	) startnOutg None
	in
	let storePlaceName = RLMap.find "name" storePlace.attrs
	in
	let myOwnProcPtr = IdtMap.find startNode.id procpointers
(*		let containmentEdgeId = grreprIncomingEdgeOfKind grrepr startNode.id EOPContain
		in
		let containmentEdge = IdtMap.find containmentEdgeId grrepr.edges
		in
		let procStartEventId = List.hd (findProcessStartNodes grrepr containmentEdge.src)
		in
		IdtMap.find procStartEventId procpointers
*)	in
	let rec createsrccheck srcprptr = function
		| [] -> DEOp (OPBoolConst false, [])
		| [myOwnProcPtr] -> DEPtrSrcCheck (myOwnProcPtr, Right srcprptr)
		| myOwnProcPtr :: ll -> DEOp (OPOr, [DEPtrSrcCheck (myOwnProcPtr, Right srcprptr); createsrccheck srcprptr ll])
	in
	let checksAndCopies = List.map (fun (msgflowedge, srcprptr, (srcdatanode : nodeonpicturetype)) ->
		let gtask = GuardTask ("check the source of the message", (if srcprptr = NewName.invalid_id then DEOp (OPBoolConst true, []) else createsrccheck srcprptr (IdtSet.elements myOwnProcPtr)), [])
		in
		let srcdsname = RLMap.find "name" srcdatanode.attrs
		in
		let copyScript = RLMap.fold (fun compname _ ll ->
			((storePlaceName, compname), DEVar (srcdsname, compname)) :: ll
		) (snd (RLMap.find srcdsname dsdecls)) []
		in
		let taskDefCont = (copyScript, [(myOwnProcPtr, srcdsname)], [storePlaceName])
		in
		let copytaskname = "Copy the dataset " ^ srcdsname
		in
		let wholeCopyTask = if IdtSet.mem storePlace.id updDatasets then UpdateTask (copytaskname, taskDefCont) else NormalTask (copytaskname, taskDefCont)
		in
		(gtask, wholeCopyTask)
	) receivings
	in
	let rec turnToCopy = function
		| [] -> SPRNil
		| [(_, wholeCopyTask)] -> SPRTask wholeCopyTask
		| (gtask, wholeCopyTask) :: ll -> SPRBranch (gtask ,SPRTask wholeCopyTask, (turnToCopy ll))
	in
	turnToCopy checksAndCopies
and (iterMakeProcStartingFromNode : graphgraphtype -> datasetdeclaration RLMap.t * componentdefinition list IdtMap.t * definingexpr IdtMap.t -> NewName.idtype option list list IdtMap.t -> IdtSet.t IdtMap.t -> IdtSet.t -> RLSet.t -> NewName.idtype -> anyproc) = fun grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets startNodeId ->
	match makeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets startNodeId with
		| Left (stproc, nextnodeid, _) -> PRSeq (stproc, iterMakeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets nextnodeid)
		| Right aproc -> aproc
and (addToNetworkFromNode : graphgraphtype -> datasetdeclaration RLMap.t * componentdefinition list IdtMap.t * definingexpr IdtMap.t -> NewName.idtype option list list IdtMap.t -> IdtSet.t IdtMap.t -> IdtSet.t -> RLSet.t -> NewName.idtype -> (* stoppingproc array * sprNetworkNode array -> (int, int) either IdtMap.t -> *) stoppingproc array * sprNetworkNode array * ((int * anyproc) list, (NewName.idtype * NewName.idtype) option) either ) = fun grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets startNodeId (* (existingNWNodes, existingNWPoints) nodesToNWMap *) ->
	let rec collectLhsOfCompDefs = function
		| [] -> RLSet.empty
		| ((dsname,_),_) :: cdefs -> RLSet.add dsname (collectLhsOfCompDefs cdefs)
	in
	let rec collectRhsOfCompDef = function
		| DEVar (dsname,_) -> RLSet.singleton dsname
		| DEOp (_, defs)
		| DEAppl (_, defs) -> List.fold_right RLSet.union (List.map collectRhsOfCompDef defs) RLSet.empty
		| _ -> RLSet.empty
	in
	let rec collectRhsOfManyCompDef = function
		| [] -> RLSet.empty
		| (_,defs) :: cdefs -> RLSet.union (collectRhsOfCompDef defs) (collectRhsOfManyCompDef cdefs)
	in
	let updDatasetsAsStrings = IdtSet.fold (fun dsid ss ->
		let (dsnode,_,_) = IdtMap.find dsid grrepr.nodes
		in
		RLSet.add (RLMap.find "name" dsnode.attrs) ss
	) updDatasets RLSet.empty
	in
	let workq = Queue.create ()
	and handledNodes = ref (IdtSet.singleton startNodeId)
	and handledEdges = ref IdtMap.empty
	and collectedNWedges = EASP.create ()
	and collectedNWnodes = EASNN.create ()
	and outgoingProcs = ref []
	and pastFinalNode = ref None
	and loopDetection = ref None
	and rightHandAnswer = ref None
	in
	EASP.appendV collectedNWedges SPRNil;
	Queue.add (startNodeId, NewName.invalid_id) workq;
	while not (Queue.is_empty workq) do
		let (workNodeId, comeFromEdgeId) = Queue.take workq
		in
		let (workNode, wnoutg, wnincom) = IdtMap.find workNodeId grrepr.nodes
		in
		let chwnoutg = ref wnoutg
		in
		if (comeFromEdgeId = NewName.invalid_id) || (IdtSet.for_all (fun incedgeid ->
			let incedge = IdtMap.find incedgeid grrepr.edges
			in
			(incedge.kind <> EOPSeqFlow) || (IdtMap.mem incedgeid !handledEdges)
		) wnincom) then
		begin
			loopDetection := None;
			let possMyLoc = ref None
			in
			let placeTheTask wholeTask =
				let checkPreviousPlace = if comeFromEdgeId = NewName.invalid_id then Left 0 else IdtMap.find comeFromEdgeId !handledEdges
				in
				match checkPreviousPlace with
					| Left c ->
						let existProc = EASP.getV collectedNWedges c
						in
						(EASP.setV collectedNWedges c (SPRSeq (existProc, wholeTask));
						possMyLoc := Some (Left c) )
					| Right c -> (
						EASP.appendV collectedNWedges wholeTask;
						let wtidx = (EASP.getLen collectedNWedges) - 1
						in
						possMyLoc := Some (Left wtidx);
						match (EASNN.getV collectedNWnodes c) with
							| SPRNBranch (in_c, gtask, t_c, f_c) ->
							begin
								let comeFromEdge = IdtMap.find comeFromEdgeId grrepr.edges
								in
								if (RLMap.find "branch" comeFromEdge.attrs) = "true" then
									EASNN.setV collectedNWnodes c (SPRNBranch (in_c, gtask, wtidx, f_c))
								else
									EASNN.setV collectedNWnodes c (SPRNBranch (in_c, gtask, t_c, wtidx))
							end
							| SPRNJoin (in_cl, _) ->
							begin
								EASNN.setV collectedNWnodes c (SPRNJoin (in_cl, wtidx))
							end
					)
			in
			let placeTheTail wholeTail =
				let contAfterIdx =
					placeTheTask SPRNil;
					let Some (Left c) = !possMyLoc
					in c
				in
				outgoingProcs := (contAfterIdx, wholeTail) :: !outgoingProcs
			in
(*			let workNodeHasCode = IdtMap.mem workNodeId taskprogs (* Alternatively: worknode.attrs has element "sql" or "skencrypt" or "skdecrypt" *)  *)
			let workNodeHasCode = (RLMap.mem "sql" workNode.attrs) || (RLMap.mem "skencrypt" workNode.attrs) || (RLMap.mem "skdecrypt" workNode.attrs) || (RLMap.mem "abencrypt" workNode.attrs) || (RLMap.mem "abdecrypt" workNode.attrs) || (RLMap.mem "pkencrypt" workNode.attrs) || (RLMap.mem "pkdecrypt" workNode.attrs)
			in
			if workNode.kind = NOPTask then
			begin
				(if IdtMap.mem workNodeId guards then
				begin
					let fromEdgeNo = if comeFromEdgeId = NewName.invalid_id then 0 else
						match IdtMap.find comeFromEdgeId !handledEdges with
							| Left c -> c
							| Right c -> (
								placeTheTask SPRNil;
								let Some (Left c') = !possMyLoc
								in
								possMyLoc := None;
								c'
							)
					in
					let gdef = IdtMap.find workNodeId guards
					in
					let srcdss = RLSet.fold (fun dsname ll -> (IdtSet.empty, dsname) :: ll) (collectRhsOfCompDef gdef) []
					in
					let guardToGatewayEdgeId = grreprOutgoingEdgeOfKind grrepr workNodeId EOPSeqFlow
					in
					let guardToGatewayEdge = IdtMap.find guardToGatewayEdgeId grrepr.edges
					in
					let (gwnode, gwoutg, gwincom) = IdtMap.find guardToGatewayEdge.tgt grrepr.nodes
					in
					EASNN.appendV collectedNWnodes (SPRNBranch (fromEdgeNo, GuardTask ((RLMap.find "name" workNode.attrs), gdef, srcdss), -1, -1));
					possMyLoc := Some (Right ((EASNN.getLen collectedNWnodes) - 1));
					handledNodes := IdtSet.add gwnode.id !handledNodes;
					chwnoutg := gwoutg
				end
				else if (IdtMap.mem workNodeId taskprogs) && workNodeHasCode then
				begin
					let compdefs = IdtMap.find workNodeId taskprogs
					in
					let lhsdss = collectLhsOfCompDefs compdefs
					and rhsdss = collectRhsOfManyCompDef compdefs
					in
					let noderhscomp = RLSet.fold (fun dsname ll ->
						(IdtSet.empty, dsname) :: ll
					) rhsdss []
					and (nodelhscomp, pubcomp) = RLSet.fold (fun dsname (ll, pp) ->
						let ll' = dsname :: ll
						and pp' = if RLSet.mem dsname publishDatasets then (SPRPublish (None, dsname)) :: pp else pp
						in (ll', pp')
					) lhsdss ([], [])
					in
					let taskContent =
						if RLSet.is_empty (RLSet.inter updDatasetsAsStrings lhsdss) then
							NormalTask ((RLMap.find "name" workNode.attrs), (compdefs, noderhscomp, nodelhscomp))
						else
							UpdateTask ((RLMap.find "name" workNode.attrs), (compdefs, noderhscomp, nodelhscomp))
					in
					let wholeTask = List.fold_right (fun tsk proc ->
						SPRSeq (proc, tsk)
					) pubcomp (SPRTask taskContent)
					in
					placeTheTask wholeTask
				end
				else if IdtSet.exists (fun outgEdgeId ->
					let outgEdge = IdtMap.find outgEdgeId grrepr.edges
					in
					if outgEdge.kind <> EOPMsgFlow then false else
					let (cEvent,_,_) = IdtMap.find outgEdge.tgt grrepr.nodes
					in
					(cEvent.kind = NOPEvent) && ((RLMap.find "eventkind" cEvent.attrs) = "start")
				) wnoutg then
				begin
					let prptr = IdtSet.choose (IdtMap.find workNodeId procpointers)
					and myTaskName = RLMap.find "name" workNode.attrs
					and procAddr = List.map (function | None -> None | Some prnodeid -> 
						let (prnode, _, _) = IdtMap.find prnodeid grrepr.nodes
						in
						Some (RLMap.find "name" prnode.attrs)
					) (List.hd (IdtMap.find workNodeId msgFlowPaths))
					in
					placeTheTask (SPRTask (ProcLauncher (myTaskName, prptr, procAddr)))
				end
				else
					placeTheTask SPRNil
				);
				let Some myLoc = !possMyLoc
				in
				IdtSet.iter (fun outedgeid ->
					let outedge = IdtMap.find outedgeid grrepr.edges
					in
					if outedge.kind <> EOPSeqFlow then ()
					else
					(handledEdges := IdtMap.add outedgeid myLoc !handledEdges;
					(if not (IdtSet.mem outedge.tgt !handledNodes) then
					begin
						handledNodes := IdtSet.add outedge.tgt !handledNodes;
						Queue.add (outedge.tgt, outedgeid) workq
					end))
				) !chwnoutg
			end
			else if workNode.kind = NOPEvent then (* not startevent *)
			begin
				(if ((RLMap.find "eventkind" workNode.attrs) = "catch") && ((RLMap.find "eventtype" workNode.attrs) = "message") then
				begin
					let readSProc = collectReceivings grrepr (workNode, wnoutg, wnincom) procpointers dsdecls updDatasets
					in
					placeTheTask readSProc;
				end
				else
				begin
					placeTheTask SPRNil
				end);
				let Some myLoc = !possMyLoc
				in
				IdtSet.iter (fun outedgeid ->
					let outedge = IdtMap.find outedgeid grrepr.edges
					in
					if outedge.kind <> EOPSeqFlow then ()
					else
					(handledEdges := IdtMap.add outedgeid myLoc !handledEdges;
					(if not (IdtSet.mem outedge.tgt !handledNodes) then
					begin
						handledNodes := IdtSet.add outedge.tgt !handledNodes;
						Queue.add (outedge.tgt, outedgeid) workq
					end))
				) wnoutg
			end
			else if workNode.kind = NOPGateway then
			begin
				if (RLMap.find "gatewaykind" workNode.attrs) = "parallel" then
				begin
					match makeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets workNodeId with
						| Left (sproc, nextNodeId, befNextEdgeId) ->
						begin
							placeTheTask sproc;
							let Some myLoc = !possMyLoc
							in
							handledEdges := IdtMap.add befNextEdgeId myLoc !handledEdges;
							(if not (IdtSet.mem nextNodeId !handledNodes) then
							begin
								handledNodes := IdtSet.add nextNodeId !handledNodes;
								Queue.add (nextNodeId, befNextEdgeId) workq
							end)
						end
						| Right aproc ->
						begin
							placeTheTail aproc
						end
				end
				else if (RLMap.find "gatewaykind" workNode.attrs) = "exclusive" then
				begin
					let incomingList = IdtSet.fold (fun incedgeid ll ->
						let incedge = IdtMap.find incedgeid grrepr.edges
						in
						if incedge.kind <> EOPSeqFlow then ll else
						match (IdtMap.find incedgeid !handledEdges) with
							| Left c -> c :: ll
							| Right c ->
							begin
								EASP.appendV collectedNWedges SPRNil;
								let res = (EASP.getLen collectedNWedges) - 1
								in
								(match (EASNN.getV collectedNWnodes c) with
									| SPRNBranch (in_c, gtask, t_c, f_c) ->
									begin
										let comeFromEdge = IdtMap.find incedgeid grrepr.edges
										in
										if (RLMap.find "branch" comeFromEdge.attrs) = "true" then
											EASNN.setV collectedNWnodes c (SPRNBranch (in_c, gtask, res, f_c))
										else
											EASNN.setV collectedNWnodes c (SPRNBranch (in_c, gtask, t_c, res))
									end
									| SPRNJoin (in_cl, _) ->
									begin
										EASNN.setV collectedNWnodes c (SPRNJoin (in_cl, res))
									end);
								res :: ll
							end
					) wnincom []
					in
					EASNN.appendV collectedNWnodes (SPRNJoin (incomingList, -1));
					let myLoc = (EASNN.getLen collectedNWnodes) - 1
					in
					IdtSet.iter (fun outedgeid ->
						let outedge = IdtMap.find outedgeid grrepr.edges
						in
						if outedge.kind <> EOPSeqFlow then ()
						else
						(handledEdges := IdtMap.add outedgeid (Right myLoc) !handledEdges;
						(if not (IdtSet.mem outedge.tgt !handledNodes) then
						begin
							handledNodes := IdtSet.add outedge.tgt !handledNodes;
							Queue.add (outedge.tgt, outedgeid) workq
						end))
					) wnoutg
				end
				else
					raise (Failure "got a gateway that is neither parallel or exclusive")
			end
			else if workNode.kind = NOPDataset then raise (Failure "trying to convert a dataset at extendNW")
			else (* workNode.kind = NOPSubprocess *)
			begin
				let Right aproc = makeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgFlowPaths procpointers updDatasets publishDatasets workNodeId
				in
				placeTheTail aproc
			end
		end
		else
		begin
			if !loopDetection = None then
			begin
				loopDetection := Some (workNodeId, comeFromEdgeId);
				Queue.add (workNodeId, comeFromEdgeId) workq
			end
			else
			begin
				Queue.add (workNodeId, comeFromEdgeId) workq;
				if Some (workNodeId, comeFromEdgeId) = !loopDetection then
				begin
					if (Queue.length workq) > 1 then raise (Failure "Network has several potential endings")
					else
					if not ((workNode.kind = NOPGateway) && ((RLMap.find "gatewaykind" workNode.attrs) = "parallel")) then
						raise (Failure "the ending node of the Network is not a parallel gateway")
					else
					begin
						rightHandAnswer := Some (workNodeId, comeFromEdgeId);
						Queue.clear workq
					end
				end
			end
		end
	done;
	match !rightHandAnswer with
	|	None -> (EASP.getArray collectedNWedges, EASNN.getArray collectedNWnodes, Left !outgoingProcs)
	|	Some (nid, eid) -> if !outgoingProcs = [] then (EASP.getArray collectedNWedges, EASNN.getArray collectedNWnodes, Right (Some (nid, eid))) else (raise (Failure "Network ends with both tails and a final node"))
;;

let printgrgr grrepr fn =
	let myEscape s =
		let rec findAndHash i =
			if i >= (String.length s) then raise Not_found else
			let j = String.index_from s i '&'
			in
			if (j+1) >= (String.length s) then raise Not_found else
			if s.[j+1] = '#' then j else findAndHash (j+1)
		in
		String.escaped (try
			String.sub s 0 (findAndHash 0)
		with Not_found -> s)
	in
	let oc = open_tmpout fn
	in
	let output_node (node : nodeonpicturetype) =
		output_string oc ("v" ^ (NewName.to_string node.id) ^ " [shape=");
		output_string oc (
			match node.kind with
				| NOPTask -> "box"
				| NOPDataset -> "note"
				| NOPSubprocess -> "box"
				| NOPPool -> "hexagon"
				| NOPGateway -> "diamond"
				| NOPEvent -> "circle"
				| NOPComment -> "underline" );
		output_string oc " style=";
		output_string oc (
			match node.kind with
				| NOPTask -> "rounded"
				| NOPDataset -> "solid"
				| NOPSubprocess -> "bold"
				| NOPPool -> "bold"
				| NOPGateway -> "solid"
				| NOPEvent -> let x = RLMap.find "eventkind" node.attrs in if x = "end" then "bold" else if x = "catch" then "dotted" else "solid"
				| NOPComment -> "solid" );
		output_string oc " label=\"";
		let collAttrs = RLMap.fold (fun attrname attrvalue ll ->
			if (attrname = "name") || (attrname = "eventkind") || (attrname = "eventtype") || (attrname = "gatewaykind") then ll else
			(attrname ^ " = " ^ attrvalue) :: ll
		) node.attrs []
		in
		let nameattr = (NewName.to_string node.id ^ ": ") ^ ( match node.kind with
			| NOPEvent -> RLMap.find "eventtype" node.attrs
			| NOPGateway -> let x = RLMap.find "gatewaykind" node.attrs in if x = "parallel" then "+" else if x = "exclusive" then "X" else x
			| _ -> (try RLMap.find "name" node.attrs with Not_found -> "NO NAME")
			)
		in
		output_string oc (String.concat "\\n" (List.map myEscape (nameattr :: collAttrs)));
		output_string oc "\"];\n"
	and output_edge edge =
		output_string oc ("v" ^ (NewName.to_string edge.src) ^ " -> v" ^ (NewName.to_string edge.tgt) ^ " [style=");
		output_string oc (
			match edge.kind with
				| EOPSeqFlow -> "solid"
				| EOPMsgFlow -> "dashed"
				| EOPRead 
				| EOPWrite -> "dotted"
				| EOPContain -> "bold"
				| EOPBoundary -> "solid"
				| EOPComment -> "dotted" );
		output_string oc " color=";
		output_string oc (
			if (RLMap.mem "default" edge.attrs) || ((RLMap.mem "branch" edge.attrs) && ((RLMap.find "branch" edge.attrs) = "false")) then "red" else
			match edge.kind with
				| EOPSeqFlow -> "black"
				| EOPMsgFlow -> "black"
				| EOPRead 
				| EOPWrite -> "black"
				| EOPContain -> "green"
				| EOPBoundary -> "blue"
				| EOPComment -> "black" );
		let collAttrs = ("ID = " ^ NewName.to_string edge.id) :: (RLMap.fold (fun attrname attrvalue ll ->
			if (attrname = "default") || (attrname = "branch") then ll else
			(attrname ^ " = " ^ attrvalue) :: ll
		) edge.attrs [])
		in
		if collAttrs = [] then
		begin
			output_string oc "];\n"
		end
		else
		begin
			output_string oc " label=\"";
			output_string oc (String.concat "\\n" (List.map myEscape collAttrs));
			output_string oc "\"];\n"
		end
	in
	output_string oc "digraph {\n";
	IdtMap.iter (fun _ ((node : nodeonpicturetype),_,_) -> output_node node
	) grrepr.nodes;
	IdtMap.iter (fun _ edge -> output_edge edge
	) grrepr.edges;
	output_string oc "}\n";
	close_out oc
;;

let makeABBEKeygenProc grrepr =
	let abbedata = IdtMap.fold (fun _ ((node : nodeonpicturetype),_,_) gridToPar ->
		if RLMap.mem "abpublic" node.attrs then
		begin
			let grid = RLMap.find "abgroup" node.attrs
			and nname = RLMap.find "name" node.attrs
			in
			let (mpknames, skdescs, pkpknames, pksknames) = try RLMap.find grid gridToPar with Not_found -> (RLSet.empty, RLMap.empty, RLSet.empty, RLSet.empty)
			in
			RLMap.add grid ((RLSet.add nname mpknames), skdescs, pkpknames, pksknames) gridToPar
		end
		else if RLMap.mem "abprivate" node.attrs then
		begin
			let grid = RLMap.find "abgroup" node.attrs
			and nname = RLMap.find "name" node.attrs
			and keyattrs = readABEAttributeSetFromTaskAttrs node.attrs
			in
			let (mpknames, skdescs,pkpknames, pksknames) = try RLMap.find grid gridToPar with Not_found -> (RLSet.empty, RLMap.empty, RLSet.empty, RLSet.empty)
			in
			RLMap.add grid (mpknames, (RLMap.add nname keyattrs skdescs), pkpknames, pksknames) gridToPar
		end
		else if RLMap.mem "pkpublic" node.attrs then
		begin
			let grid = RLMap.find "pkgroup" node.attrs
			and nname = RLMap.find "name" node.attrs
			in
			let (mpknames, skdescs, pkpknames, pksknames) = try RLMap.find grid gridToPar with Not_found -> (RLSet.empty, RLMap.empty, RLSet.empty, RLSet.empty)
			in
			RLMap.add grid (mpknames, skdescs, (RLSet.add nname pkpknames), pksknames) gridToPar
		end
		else if RLMap.mem "pkprivate" node.attrs then
		begin
			let grid = RLMap.find "pkgroup" node.attrs
			and nname = RLMap.find "name" node.attrs
			in
			let (mpknames, skdescs, pkpknames, pksknames) = try RLMap.find grid gridToPar with Not_found -> (RLSet.empty, RLMap.empty, RLSet.empty, RLSet.empty)
			in
			RLMap.add grid (mpknames, skdescs, pkpknames, (RLSet.add nname pksknames)) gridToPar
		end
		else gridToPar
	) grrepr.nodes RLMap.empty
	in
	RLMap.fold (fun groupname (mpknames, skdescs, pkpknames, pksknames) (currproc, currdsdecls, currNoUpds, currForgetUpds) ->
		let mskGenTask = NormalTask (("Generate master secret key for ABBE / PK group " ^ groupname),
			([(("Master_secret_key_for_" ^ groupname, "msk"), DEOp ((if RLSet.is_empty mpknames then OPPKGenSK else OPABGenMSK), [DEVar ("Master_randomness_for_" ^ groupname, "rnd")]))],
			[(IdtSet.empty, "Master_randomness_for_" ^ groupname)],
			["Master_secret_key_for_" ^ groupname])
		)
		in
		let mpkGenTasks = RLSet.fold (fun mpkname ll ->
			(mpkname, (NormalTask (("Generate master public key for ABBE group " ^ groupname),
			([((mpkname, "key"), DEOp (OPABExtractMPK, [DEVar ("Master_secret_key_for_" ^ groupname, "msk")]))],
			[(IdtSet.empty, "Master_secret_key_for_" ^ groupname)],
			[mpkname])
			))) :: ll
		) mpknames []
		in
		let allGenTasks = RLMap.fold (fun skname keyattrs ll ->
			(skname, NormalTask (("Generate secret key for ABBE group " ^ groupname ^ " with attributes " ^ (String.concat ", " (RLSet.elements keyattrs))),
			([((skname, "key"), DEOp (OPABExtractSK keyattrs, [DEVar ("Master_secret_key_for_" ^ groupname, "msk")]))],
			[(IdtSet.empty, "Master_secret_key_for_" ^ groupname)],
			[skname])
			)) :: ll
		) skdescs mpkGenTasks
		in
		let pkpkGenTasks = RLSet.fold (fun pkname ll ->
			(pkname, (NormalTask (("Extract public key for PK group " ^ groupname),
			([((pkname, "key"), DEOp (OPPKExtractPK, [DEVar ("Master_secret_key_for_" ^ groupname, "msk")]))],
			[(IdtSet.empty, "Master_secret_key_for_" ^ groupname)],
			[pkname])
			))) :: ll
		) pkpknames allGenTasks
		in
		let pkskGenTasks = RLSet.fold (fun skname ll ->
			(skname, (NormalTask (("Copy private key for PK group " ^ groupname),
			([((skname, "key"), DEVar ("Master_secret_key_for_" ^ groupname, "msk"))],
			[(IdtSet.empty, "Master_secret_key_for_" ^ groupname)],
			[skname])
			))) :: ll
		) pksknames pkpkGenTasks
		in
		let mrnddecl = ("Master_randomness_for_" ^ groupname, RLMap.singleton "rnd" VAny)
		and mskdecl = ("Master_secret_key_for_" ^ groupname, RLMap.singleton "msk" VAny)
		in
		let newproc = SPRSeq ((SPRTask mskGenTask), (List.fold_right (fun (_,atask) pr -> SPRSeq ((SPRTask atask), pr)) pkskGenTasks currproc))
		and newdsdecls = mrnddecl :: mskdecl :: currdsdecls
		and newNoUpds = RLSet.add ("Master_randomness_for_" ^ groupname) currNoUpds
		and newForgetUpds = List.fold_right (fun (kname,_) s -> RLSet.add kname s) allGenTasks currForgetUpds
		in
		(newproc, newdsdecls, newNoUpds, newForgetUpds)
	) abbedata (SPRNil, [], RLSet.empty, RLSet.empty)
;;

let (convertXMLBPMN : string -> anyproc * datasetdeclaration list * RLSet.t) = fun fname ->
	let z nm f garg =
		let res = f garg
		in
		print_endline ("Performed step no. " ^ nm);
		areEdgesOK res;
		printgrgr res ("P_" ^ nm ^ ".dot");
		res
	in
	let xmlrepr = Xml.parse_file fname
	in
	let (grrepr0pre, idForStr) = collectFromFile xmlrepr
	in
	let grrepr0 = (z "4" joinSameNameDatasets) ((z "3" defaultsToEdgeAttrs) ((z "2b" noMultipleWrites)  ((z "2a" noMultipleMsgflows) ((z "2" commentsToAttrs) ((z "1" (fun x -> x)) grrepr0pre)))))
	in
	let grrepr1 = (z "12" copyBeforeSend) ((z "11" foldParallelParallelGW) ((z "10" replicateAfterReplicate) ((z "9" conditionalTwoMsgReceive) ((z "8" dissolveNonreplSubproc) ((z "7" handle2ndtryConstellation) ( (* (z "6" oneEndOfEachType) *) ((z "5" moveMsgFlowToStartNode) grrepr0)))))))
	in
	let grrepr = 
		let keepgoing = ref true
		and currgr = ref grrepr1
		and ix = ref 1
		in
		while !keepgoing do
			let (g,b) = replicateFollowsReplicate !currgr
			in
			currgr := g;
			keepgoing := b;
			printgrgr g ("PQ_" ^ (string_of_int !ix) ^ ".dot");
			ix := !ix + 1
		done;
		!currgr
	in
	let (dsdecls, taskprogs, guards, grrepr) = readDataDeclarations grrepr idForStr
	in
	printgrgr grrepr "PR_1.dot";
	let msgflowpaths = findMsgFlowProcPaths grrepr
	in
	print_endline "Found the following message flow paths";
	IdtMap.fold (fun nodeid ll () ->
		print_endline ("Node no. " ^ (NewName.to_string nodeid));
		List.iter (fun lll ->
			print_endline ("Possible path: [" ^ (String.concat "; " (List.map (function None -> "UP" | Some d -> NewName.to_string d) lll)) ^ "]")
		) ll
	) msgflowpaths ();
	let procpointers = introduceProcPointers grrepr msgflowpaths
	and (severalUpdates, noUpdates, noReadsPre) = manyTimesUpdatedDatasets grrepr
	and insecCommsPre = insecurelySentDatasets grrepr
	in
	print_endline "Found the following proc. pointers";
	IdtMap.fold (fun nodeid pps () ->
		print_string ("Node no: " ^ (NewName.to_string nodeid));
		print_endline (", possible pointers: {" ^ (String.concat "; " (List.map NewName.to_string (IdtSet.elements pps))) ^ "}")
	) procpointers ();
	let noReads = IdtSet.fold (fun nodeid ss ->
		let (node,_,_) = IdtMap.find nodeid grrepr.nodes
		in
		RLSet.add (RLMap.find "name" node.attrs) ss
	) (IdtSet.union noReadsPre insecCommsPre) RLSet.empty
	in
	let topProcessIds = findTopProcessNodes grrepr
	in
	let inInterm = IdtSet.fold (fun procId ll ->
		(iterMakeProcStartingFromNode grrepr (dsdecls, taskprogs, guards) msgflowpaths procpointers severalUpdates noReads procId) :: ll
	) topProcessIds []
	in
	let noUpdNames = IdtSet.fold (fun nodeid ss ->
		let (node,_,_) = IdtMap.find nodeid grrepr.nodes
		in
		RLSet.add (RLMap.find "name" node.attrs) ss
	) noUpdates RLSet.empty
	in
	let (abbekeygenproc, extradsdecls, extranoupds, forgetNoUpds) = makeABBEKeygenProc grrepr
	in
	(PRSeq (abbekeygenproc, (PRParal inInterm)), RLMap.fold (fun _ v l -> v :: l) dsdecls extradsdecls, RLSet.diff (RLSet.union extranoupds noUpdNames) forgetNoUpds)
;;

(* Steps for converting:

% . For subprocesses with multiple ends: introduce "ending place". Write to it at each end event. Make all end events plain. Immediately after the subprocess, introduce a task that reads that "ending place" and branches according to that.
. Instead of this: make sure that each _sub_process has only one end event of each type. Introduce XOR-gateways, if necessary [fun oneEndOfEachType].

. Handle constellations: Two parallel processes. Second starts with a message start event. It has a single conditional gateway, followed by a two events, one of them timer, and another one X. Second process is preceeded by two throw events, one of them a message event and the other one X. Before that, a gateway and a check that mentions timers. "Timer state" is an incoming dataset. Before that, a (reversed) path to the first process. Find, which end event of the first process corresponds to the outgoing path. Before the end event, there is a task that has a single input Y. It may be before the "ending place" writing.
	Introduce to the outside of these processes the state variables "Active process" and "State digest".
	Change the first process, as I have drawn. Remove the last task. Check "Active process". If no active process, then add a task that makes "Active process" true and make a MsgFlow to the second process (add task named "Send"), with Y as the argument. If active process is there, then overwrite "State digest" with Y and "Timer state" with "Signal".
	Change the second process, as I have drawn. At the start, the message start event stays the same. At the conditional gateway, make a task that writes "Reset" to "Timer state". Then make a task that reads "Timer state" and checks if it is "Reset" or "Signal". Then comes a normal gateway. "Reset"-branch is for the timer-expired case, and "Signal"-branch for the second-message-received case. In "Reset" branch, make "Active process" false. In "Signal branch", copy "State digest" and make "Active process" false.
	Remove the second process, the two events before it, the gateway before it, the timer check before it. Instead, make the second process run in parallel with the first one. Instead of all of this following the first process, put a normal end event.
[fun handle2ndtryConstellation]

. For each conditional gateway, introduce a "condition place" that it checks. Replace the conditional gateway with a task doing the check and a normal gateway
. If the conditional gateway was about receiving one of two messages first:
	Let the receives be in parallel with the gateway. Things that followed the receivings beforehand, will now be right after the gateway.
	Before the gateway, and parallel branch do a "reset" of the "condition place"
	After each receive, do a "write" into the "condition place".
	The parallel branches will not flow together again.
	[fun conditionalTwoMsgReceive]
. If the conditional gateway was timer vs. signal, then:
	it's a part of a larger constellation. Already handled
	[]

. MsgFlows going to a subprocess: make them go to the start event instead [fun moveMsgFlowToStartNode]

. For code following a replicated subprocess:
	Put it inside a replicated subprocess, running in parallel to that replicated subprocess
	Make it start with a message start event. Let it catch a message, which will be ignored.
	In original subprocess: before each end event, introduce a send task to the new message start event. Also, add a new data element. Let it have a single component
	This is done for each possible exit (boundary event) from the first subprocess
	[fun replicateAfterReplicate]

. Translate the scripts in tasks to the intermediate representation [fun translateTaskScript]. For each dataset that is not an input dataset (and thus has already a definition): see where it is written at. See, which fields of it are written into. Deduce its components.

. Fold parallel gateways to parallel gateways [fun foldParallelParallelGW]

. If two replicated subprocesses are running in parallel and the second starts when the first one ends (see the MsgFlow from first to second): join them into a single process, one following the other one. The subprocesses must have common immediate superprocess [fun replicateFollowsReplicate]

. Dissolve non-replicated subprocesses with one start and one end [fun dissolveNonreplSubproc]

. For each message catch event: record the path from it to the subprocess that sends the message. There may be several senders and thus several paths [fun findMsgFlowProcPaths]
. For each message send event that starts a process: record the path from it to the starting process [fun findMsgFlowProcPaths]
. Introduce a procpointer for each startevent, and for each send that starts a process. For each message catch, determine the procpointer by comparing the paths [fun introduceProcPointers]

. Starting from inner subprocesses, convert the graph into PRNetwork-s and PRParal-s
. Publish datasets if they are requested across participant boundaries

*)

(*	let thing = Xml.parse_file "../../../../share/NDN_chronosync.bpmn"
	in
	let colltags = ref RLSet.empty
	in
	printoutxml colltags 0 thing;
	print_string "\n\nTags:\n";
	RLSet.iter (fun s -> print_string s; print_newline ()) !colltags;
	let (bpir, dsdecll, inputds) = BpmnInput.convertXMLBPMN "../../../../share/NDN_chronosync.bpmn"
	in
	let dg = BpmnInput.convertBPMN bpir dsdecll inputds *)

