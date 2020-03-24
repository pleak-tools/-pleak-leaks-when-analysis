open GrbCommons;;
open GrbGraphs;;
open GrbInput;;

type bpmnfun = string;;
type procname = string;;
type datasetname = string;;
type componentname = string;;
type procpointer = NewName.idtype;;
type datasetcomponent = datasetname * componentname;;
type componentdeclaration = componentname * valuetype;;
type datasetdeclaration = datasetname * (valuetype RLMap.t);;
type definingexpr = DEIntConst of int | DEFloatConst of float | DEVar of datasetcomponent | DEAppl of bpmnfun * (definingexpr list) | DEOp of operationname * (definingexpr list) | DEPtrSrcCheck of procpointer * ((procname option list), procpointer) either | DEStringConst of string;;
type componentdefinition = datasetcomponent * definingexpr;;
type taskname = string;;
type normaltaskdefinition = (componentdefinition list) * ((IdtSet.t * datasetname) list) * (datasetname list);; (* Program, list of inputs, list of outputs *)
type taskdef = NormalTask of taskname * normaltaskdefinition | UpdateTask of taskname * normaltaskdefinition | GuardTask of taskname * definingexpr * ((IdtSet.t * datasetname) list) | StartEvent of procpointer option * taskname | ProcLauncher of taskname * procpointer * (procname option list);;
type stoppingproc = SPRNil | SPRTask of taskdef | SPRParal of stoppingproc list | SPRBranch of taskdef * stoppingproc * stoppingproc | SPRSeq of stoppingproc * stoppingproc | SPRPublish of (procpointer option) * datasetname | SPRNetwork of (stoppingproc array) * (sprNetworkNode array)
and sprNetworkNode =  SPRNBranch of int * taskdef * int * int | SPRNJoin of int list * int
;;
type anyproc = PRStop of stoppingproc | PRSeq of stoppingproc * anyproc | PRParal of anyproc list | PRBranch of taskdef * anyproc * anyproc | PRReplicate of anyproc * procname | PRNetwork of (stoppingproc array) * (sprNetworkNode array) * ((int * anyproc) list)
;;

let rec iterwithintersperse f1 f2 l = match l with
	| [] -> ()
	| [x] -> f1 x
	| (x :: xs) -> f1 x; f2 (); iterwithintersperse f1 f2 xs
;;

let rec printanyproc oc tabnum =
	let tabs = String.make (2 * tabnum) ' '
	in function
	| PRStop sproc -> output_string oc tabs; output_string oc "PRSTOP(\n"; printstoppingproc oc (tabnum + 1) sproc; output_string oc tabs; output_string oc ")\n"
	| PRSeq (sproc, aproc) -> output_string oc tabs; output_string oc "PRSEQ(\n"; printstoppingproc oc (tabnum + 1) sproc; printanyproc oc (tabnum + 1) aproc; output_string oc tabs; output_string oc ")\n"
	| PRParal aprocl -> output_string oc tabs; output_string oc "PRPARAL[\n"; List.iter (fun p -> printanyproc oc (tabnum + 1) p) aprocl; output_string oc tabs; output_string oc "]\n"
	| PRBranch (td,tproc,fproc) -> output_string oc tabs; output_string oc "PRBranch(\n"; printtask oc (tabnum + 1) td; printanyproc oc (tabnum + 1) tproc; printanyproc oc (tabnum + 1) fproc; output_string oc tabs; output_string oc ")\n"
	| PRReplicate (aproc, prname) -> output_string oc tabs; output_string oc "PRReplicate( "; output_string oc prname; output_string oc "\n"; printanyproc oc (tabnum + 1) aproc; output_string oc tabs; output_string oc ")\n"
	| PRNetwork (sproca, spnna, tails) -> output_string oc tabs; output_string oc "PRNetwork{\n"; output_string oc tabs; output_string oc "EDGES:\n"; Array.iter (fun sproc -> printstoppingproc oc (tabnum + 1) sproc) sproca; output_string oc tabs; output_string oc "NODES:\n"; Array.iter (fun nnn -> printnetworknode oc (tabnum + 1) nnn) spnna; output_string oc tabs; output_string oc "TAILS:\n"; List.iter (fun (idx,aproc) -> output_string oc tabs; output_string oc (string_of_int idx); output_string oc ":\n"; printanyproc oc (tabnum + 1) aproc) tails; output_string oc tabs; output_string oc "}\n"
and printstoppingproc oc tabnum = 
	let tabs = String.make (2 * tabnum) ' '
	in function
	| SPRNil -> output_string oc tabs; output_string oc "SPRNIL()\n"
	| SPRTask td -> output_string oc tabs; output_string oc "SPRTask(\n"; printtask oc (tabnum + 1) td; output_string oc tabs; output_string oc ")\n"
	| SPRParal sprocl -> output_string oc tabs; output_string oc "SPRPARAL[\n"; List.iter (fun p -> printstoppingproc oc (tabnum + 1) p) sprocl; output_string oc tabs; output_string oc "]\n"
	| SPRBranch (td,tproc,fproc) -> output_string oc tabs; output_string oc "SPRBranch(\n"; printtask oc (tabnum + 1) td; printstoppingproc oc (tabnum + 1) tproc; printstoppingproc oc (tabnum + 1) fproc; output_string oc tabs; output_string oc ")\n"
	| SPRSeq (sproc1,sproc2) -> output_string oc tabs; output_string oc "SPRSEQ(\n"; printstoppingproc oc (tabnum + 1) sproc1; printstoppingproc oc (tabnum + 1) sproc2; output_string oc tabs; output_string oc ")\n"
	| SPRPublish (ppropt, dsname) -> output_string oc tabs; output_string oc "SPRPublish("; output_string oc (match ppropt with None -> "None" | Some c -> NewName.to_string c); output_string oc ", "; output_string oc dsname; output_string oc ")\n"
	| SPRNetwork (sproca, spnna) -> output_string oc tabs; output_string oc "SPRNetwork{\n"; output_string oc tabs; output_string oc "EDGES:\n"; Array.iter (fun sproc -> printstoppingproc oc (tabnum + 1) sproc) sproca; output_string oc tabs; output_string oc "NODES:\n"; Array.iter (fun nnn -> printnetworknode oc (tabnum + 1) nnn) spnna; output_string oc tabs; output_string oc "}\n"
and printnetworknode oc tabnum =
	let tabs = String.make (2 * tabnum) ' '
	in function
	| SPRNBranch (isrc,td,itr,ifl) -> output_string oc tabs; output_string oc "SPRNBranch("; output_string oc (string_of_int isrc); output_string oc "\n"; printtask oc (tabnum + 1) td; output_string oc tabs; output_string oc (string_of_int itr); output_string oc " <-> "; output_string oc (string_of_int ifl); output_string oc ")\n"
	| SPRNJoin (ilist, tgt) -> output_string oc tabs; output_string oc "SPRNJoin(["; output_string oc (String.concat ";" (List.map string_of_int ilist)); output_string oc "], "; output_string oc (string_of_int tgt); output_string oc ")\n"
and printtask oc tabnum =
	let tabs = String.make (2 * tabnum) ' '
	in function
	| NormalTask (tname, tcont) -> output_string oc tabs; output_string oc "NormalTask("; output_string oc tname; output_string oc ",\n"; printtaskcont oc (tabnum + 1) tcont; output_string oc tabs; output_string oc ")\n"
	| UpdateTask (tname, tcont) -> output_string oc tabs; output_string oc "UpdateTask("; output_string oc tname; output_string oc ",\n"; printtaskcont oc (tabnum + 1) tcont; output_string oc tabs; output_string oc ")\n"
	| GuardTask (tname, defexpr, inplist) -> output_string oc tabs; output_string oc "GuardTask("; output_string oc tname; output_string oc ", "; printdexpr oc defexpr; output_string oc ", "; printinplist oc inplist; output_string oc ")\n"
	| StartEvent (prptropt, tname) -> output_string oc tabs; output_string oc "StartEvent("; output_string oc tname; output_string oc ", "; output_string oc (match prptropt with None -> "None" | Some c -> NewName.to_string c); output_string oc ")\n"
	| ProcLauncher (tname, prptr, prnlist) -> output_string oc tabs; output_string oc "ProcLauncher("; output_string oc tname; output_string oc ", "; output_string oc (NewName.to_string prptr); output_string oc ", "; printprnlist oc prnlist; output_string oc ")\n"
and printinplist oc inplist = output_string oc "["; output_string oc (String.concat "; " (List.map (fun (prptropt, dsname) -> dsname ^ "@" ^ (if IdtSet.is_empty prptropt then "Here" else "{" ^ (String.concat ", " (List.map NewName.to_string (IdtSet.elements prptropt))) ^ "}")   ) inplist)); output_string oc "]"
and printprnlist oc prnlist = output_string oc "["; output_string oc (String.concat " -> " (List.map (function None -> "UP" | Some s -> s) prnlist)); output_string oc "]"
and printdexpr oc = function
	| DEIntConst c -> output_string oc (string_of_int c)
	| DEFloatConst c -> output_string oc (string_of_float c)
	| DEVar (dsname, compname) -> output_string oc dsname; output_string oc "."; output_string oc compname
	| DEAppl (fnname, args) -> output_string oc fnname; output_string oc "("; iterwithintersperse (printdexpr oc) (fun () -> output_string oc ", ") args; output_string oc ")"
	| DEOp (opname, args) -> output_string oc (string_of_opname opname); output_string oc "("; iterwithintersperse (printdexpr oc) (fun () -> output_string oc ", ") args; output_string oc ")"
	| DEPtrSrcCheck (cptr, Right optr) -> output_string oc "SrcCheck("; output_string oc (NewName.to_string cptr); output_string oc " is backwards "; output_string oc (NewName.to_string optr); output_string oc ")"
	| DEPtrSrcCheck (cptr, Left prnlist) -> output_string oc "SrcCheck("; output_string oc (NewName.to_string cptr); output_string oc " is from "; printprnlist oc prnlist; output_string oc ")"
	| DEStringConst c -> output_string oc "\""; output_string oc c; output_string oc "\""
and printtaskcont oc tabnum (compdefl, inpl, outpl) =
	let tabs = String.make (2 * tabnum) ' '
	in
	output_string oc tabs; output_string oc "DEFINITIONS:\n";
	List.iter (fun ((lhsds, lhscomp), rhs) -> output_string oc tabs; output_string oc lhsds; output_string oc "."; output_string oc lhscomp; output_string oc " = "; printdexpr oc rhs; output_string oc "\n" ) compdefl;
	output_string oc tabs; output_string oc "INPUTS:\n";
	List.iter (fun (prptropt,dsname) -> output_string oc tabs; output_string oc (dsname ^ "@" ^ (if IdtSet.is_empty prptropt then "Here" else "{" ^ (String.concat ", " (List.map NewName.to_string (IdtSet.elements prptropt))) ^ "}") ^ "\n" )) inpl;
	output_string oc tabs; output_string oc "OUTPUTS: "; output_string oc (String.concat ", " outpl); output_string oc "\n"
;;

type prptrdesctype = {
(*	tgt : procname option list; *)
	checknodeid : GrbInput.attrlocationtype; (* ID of the AND-node *)
	kcechnodeid : GrbInput.attrlocationtype; (* ID of the Naeloob-typed AND-node *)
	procpath : procname list; (* the innermost starts the list *)
	numdatadims : int;
	numjointdims : int; (* how many dimensions the initiator and target have in common *)
	backptr : procpointer;
};;

type datasetlocationtype = {
	dsl_exec : GrbInput.attrlocationtype;			(* existence node *)
	dsl_cexe : GrbInput.attrlocationtype;			(* existence node; Naeloob-typed *)
	dsl_time : GrbInput.attrlocationtype;			(* timing node *)
	dsl_attr : GrbInput.attrlocationtype RLMap.t;	(* nodes of the attributes of the dataset *)
	dsl_ixt : indextypetype;						(* indextype of everything *)
};;

(*type datasetlocationtype = GrbInput.attrlocationtype * GrbInput.attrlocationtype * (GrbInput.attrlocationtype RLMap.t) * indextypetype;; ** exist node, time node, attribute nodes, indextype of everything *)

type persistencykindtype = (* PersSet | *) PersVar | PersWriteOnce of (GrbInput.attrlocationtype * GrbInput.attrlocationtype) RLMap.t;; (* determined from the name of the dataset. For writeonce, saves the location of the node that computes, whether a particular write (given by the name of the UpdateTask) is a real write. Also saves the negation of being of real write *)

type persistentwritetype = {
	timepointnode : GrbInput.attrlocationtype;
	maxnode : GrbInput.attrlocationtype;
	existnode : GrbInput.attrlocationtype;
	tsixenode : GrbInput.attrlocationtype;
	updatenode : GrbInput.attrlocationtype RLMap.t; (* indexed with names of the components of the data set *)
};;

type persistentdesctype = {
	dataixt : indextypetype;
	updatemode : persistencykindtype;
	writings : persistentwritetype RLMap.t; (* indexed with names of update tasks *)
	writecomparenodes : GrbInput.attrlocationtype RLMap.t RLMap.t (* indexed with ordered pairs of names of update tasks. The outer name is the "earlier" write, the inner name the "later" write *)
};;

type graphpreparationtype = {
	pcname : procname list;
	currixt : indextypetype;
	atprocstart : bool;
	inpdatasets : RLSet.t;	(* each input dataset will be read by just a single task beside it *)
	datasetdecls : datasetdeclaration RLMap.t;
	datasets : (datasetlocationtype * bool) RLMap.t;
	persistents : persistentdesctype RLMap.t;
	prptrs : prptrdesctype list IdtMap.t;
};;

let mergeTwoPaths _ pp1 pp2 = match pp1, pp2 with
	| None, None -> None
	| None, Some _ -> pp2
	| Some _, None -> pp1
	| Some (AITT ap1), Some (AITT ap2) ->
		let maxLen = min (Array.length ap1.(0)) (Array.length ap2.(0))
		in
		let fLen = ref 0
		and isMismatch = ref false
		in
		for i = 0 to (maxLen - 1) do
			if !isMismatch then () else
			if ap1.(0).(i) <> ap2.(0).(i) then isMismatch := true else
			fLen := i+1
		done;
		Some (AITT [| Array.sub ap1.(0) 0 !fLen |])
;;

let rec (findSBPDatasetDimensions : indextypetype -> stoppingproc -> indextypetype RLMap.t) = fun currixt sproc -> match sproc with
	| SPRNil -> RLMap.empty
	| SPRTask btask -> findTaskDatasetDimensions currixt btask
	| SPRParal sprocl -> List.fold_right (RLMap.merge mergeTwoPaths) (List.map (findSBPDatasetDimensions currixt) sprocl) RLMap.empty
	| SPRBranch (btask,tproc,fproc) -> RLMap.merge mergeTwoPaths (findTaskDatasetDimensions currixt btask) (RLMap.merge mergeTwoPaths (findSBPDatasetDimensions currixt tproc) (findSBPDatasetDimensions currixt fproc))
	| SPRSeq (tproc,fproc) -> RLMap.merge mergeTwoPaths (findSBPDatasetDimensions currixt tproc) (findSBPDatasetDimensions currixt fproc)
	| SPRPublish _ -> RLMap.empty
	| SPRNetwork (sproca, sprnna) ->
		RLMap.merge mergeTwoPaths
		(
			Array.fold_right (RLMap.merge mergeTwoPaths) (Array.map (findSBPDatasetDimensions currixt) sproca) RLMap.empty
		) (
			Array.fold_right (RLMap.merge mergeTwoPaths) (Array.map (findSPRNDatasetDimensions currixt) sprnna) RLMap.empty
		)
and (findTaskDatasetDimensions : indextypetype -> taskdef -> indextypetype RLMap.t) = fun currixt btask -> match btask with
	| NormalTask (_,(_,rds,_))
	| UpdateTask (_,(_,rds,_))
	| GuardTask (_,_,rds) ->
		let wrts = (match btask with NormalTask (_,(_,_,w)) | UpdateTask (_,(_,_,w)) -> w | _ -> [])
		in
		let localrds = List.map snd (List.filter (fun (s,_) -> IdtSet.is_empty s) rds)
		in
		List.fold_right (fun dsname mm ->
			RLMap.add dsname currixt mm
		) (localrds @ wrts) RLMap.empty
	| _ -> RLMap.empty
and (findSPRNDatasetDimensions : indextypetype -> sprNetworkNode -> indextypetype RLMap.t) = fun currixt sprnn -> match sprnn with
	| SPRNBranch (_,btask,_,_) -> findTaskDatasetDimensions currixt btask
	| _ -> RLMap.empty
and (findBPDatasetDimensions : indextypetype -> anyproc -> indextypetype RLMap.t) = fun currixt proc -> match proc with
	| PRStop sproc -> findSBPDatasetDimensions currixt sproc
	| PRSeq (sproc, nproc) -> RLMap.merge mergeTwoPaths (findSBPDatasetDimensions currixt sproc) (findBPDatasetDimensions currixt nproc)
	| PRParal procl -> List.fold_right (RLMap.merge mergeTwoPaths) (List.map (findBPDatasetDimensions currixt) procl) RLMap.empty
	| PRBranch (btask,tproc,fproc) -> RLMap.merge mergeTwoPaths (findTaskDatasetDimensions currixt btask) (RLMap.merge mergeTwoPaths (findBPDatasetDimensions currixt tproc) (findBPDatasetDimensions currixt fproc))
	| PRReplicate (rproc,dimname) ->
		let (AITT aa) = currixt
		in
		let an = Array.append aa.(0) [| (VInteger, Some dimname) |]
		in
		let newixt = (AITT [| an |])
		in
		findBPDatasetDimensions newixt rproc
	| PRNetwork (sproca, sprnna, pridxl) ->
		let v1 = RLMap.merge mergeTwoPaths
		(
			Array.fold_right (RLMap.merge mergeTwoPaths) (Array.map (findSBPDatasetDimensions currixt) sproca) RLMap.empty
		) (
			Array.fold_right (RLMap.merge mergeTwoPaths) (Array.map (findSPRNDatasetDimensions currixt) sprnna) RLMap.empty
		)
		and v2 = List.fold_right (RLMap.merge mergeTwoPaths) (List.map (fun (_,p) -> findBPDatasetDimensions currixt p) pridxl) RLMap.empty
		in
		RLMap.merge mergeTwoPaths v1 v2
;;

let rec (findSBPDataSets : stoppingproc -> datasetdeclaration RLMap.t -> RLSet.t -> RLSet.t -> indextypetype -> indextypetype RLMap.t -> DG.t -> (datasetlocationtype * bool) RLMap.t * DG.t) = fun sproc dsdescs inpdatasets persistents currixt dsdims dg0 ->
let handleTaskDataFlow m dg' dsname execkind cexebuildinstrs timekind mainkind =
	let dataixt = RLMap.find dsname dsdims
	in
	let (AITT aa) = dataixt
	in
	let ixmap = IxM [| Some ((), 0, Array.init (Array.length aa.(0)) (fun x -> x)) |]
	in
	let (_,thisdsdecl) = RLMap.find dsname dsdescs
	in
	let currdg = ref dg'
	in
	let execnode = {
		nkind = execkind;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = dataixt;
		outputindextype = dataixt;
		ixtypemap = ixmap;
	}
	and timenode = {
		nkind = timekind;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = dataixt;
		outputindextype = dataixt;
		ixtypemap = ixmap;
	}
	in
	currdg := DG.addnode execnode (DG.addnode timenode !currdg);
	let (_,cexenodeid) = List.fold_left (fun (prevconstrnodeids,_) (kindsp,xnodeinps) ->
		let xnode = {
			nkind = kindsp;
			id = NewName.get ();
			inputs = PortMap.empty;
			inputindextype = dataixt;
			outputindextype = dataixt;
			ixtypemap = ixmap;
		}
		in
		currdg := DG.addnode xnode !currdg;
		List.iter (fun (inpidx, prt) ->
			currdg := DG.addedge ((identityIndexMap prevconstrnodeids.(inpidx) dataixt, NewName.get ()), xnode.id, prt) !currdg
		) xnodeinps;
		((Array.append prevconstrnodeids [| xnode.id |]), xnode.id)
	) ([| execnode.id |], NewName.invalid_id) cexebuildinstrs
	in
	let locnodes = RLMap.fold (fun compname compval mm ->
		let locnode = {
			nkind = mainkind compval (dsname ^ "." ^ compname);
			id = NewName.get ();
			inputs = PortMap.empty;
			inputindextype = dataixt;
			outputindextype = dataixt;
			ixtypemap = ixmap;
		}
		in
		currdg := DG.addnode locnode !currdg;
		print_string ("handleTaskDataFlow created node no. " ^ (NewName.to_string locnode.id) ^ " for the dataset component " ^ dsname ^ "." ^ compname ^ "\n");
		RLMap.add compname {l = locnode.id; t = RLSet.singleton dsname} mm
	) thisdsdecl RLMap.empty
	in
	(RLMap.add dsname ({dsl_exec = {l = execnode.id; t = RLSet.singleton dsname}; dsl_cexe = {l = cexenodeid; t = RLSet.singleton dsname}; dsl_time = {l = timenode.id; t = RLSet.singleton dsname}; dsl_attr = locnodes; dsl_ixt = dataixt}, false) m, !currdg)
in
let handleTaskOutput dg0 btask = match btask with
	| NormalTask (tname, (_, _, dsnl))
	| UpdateTask (tname, (_, _, dsnl)) ->
		List.fold_right (fun dsname (m, dg') ->
			if RLSet.mem dsname persistents then
			begin
				(RLMap.add dsname ({dsl_exec = {l = NewName.invalid_id; t = RLSet.empty;}; dsl_cexe = {l = NewName.invalid_id; t = RLSet.empty;}; dsl_time = {l = NewName.invalid_id; t = RLSet.empty;}; dsl_attr = RLMap.empty; dsl_ixt = AITT [||] }, true) m, dg')
			end
			else
			begin
				print_string ("handleTaskOutput now calling; arg = " ^ tname ^ "\n");
				handleTaskDataFlow m dg' dsname nkOr [(nkOrDT, [])] (nkMerge VTimePoint) (fun x y -> nkMerge x)
			end
		) dsnl (RLMap.empty, dg0)
	| _ -> (RLMap.empty, dg0)
and handleTaskInput dg0 btask = match btask with
	| NormalTask (tname, (_, inpds, _))
	| UpdateTask (tname, (_, inpds, _))
	| GuardTask (tname, _, inpds) ->
		List.fold_right (fun (_, dsname) (m, dg') ->
			if (RLSet.mem dsname inpdatasets) && (not (RLSet.mem dsname persistents)) then
			begin
				print_string ("handleTaskInput now calling; arg = " ^ tname ^ "\n");
				handleTaskDataFlow m dg' dsname (nkInputExists dsname) [(nkNot, [(0, PortUSingleB)]);(nkNotFlip false, [(1, PortSingleB true)])] nkZeroTimePoint (fun x y -> nkInput x y false)
			end
			else (m, dg')
		) inpds (RLMap.empty, dg0)
	| _ -> (RLMap.empty, dg0)
in
match sproc with
| SPRNil -> (RLMap.empty, dg0)
| SPRTask btask -> 
	let (m1, dg1) = handleTaskOutput dg0 btask
	in
	let (m2, dg2) = handleTaskInput dg1 btask
	in
	(RLMap.union m1 m2, dg2)
| SPRParal sprlist ->
	List.fold_right (fun spr (m, dg') ->
		let (m', dg'') = findSBPDataSets spr dsdescs inpdatasets persistents currixt dsdims dg'
		in (RLMap.union m m', dg'')
	) sprlist (RLMap.empty, dg0)
| SPRBranch (btask, tproc, fproc) ->
	let (m1, dg1) = handleTaskInput dg0 btask
	in
	let (m2, dg2) = findSBPDataSets tproc dsdescs inpdatasets persistents currixt dsdims dg1
	in
	let (m3, dg3) = findSBPDataSets fproc dsdescs inpdatasets persistents currixt dsdims dg2
	in
	(RLMap.union m1 (RLMap.union m2 m3), dg3)
| SPRNetwork (spredges, sprnodes) ->
	let (m1, dg1) = Array.fold_right (fun spr (m, dg') ->
		let (m', dg'') = findSBPDataSets spr dsdescs inpdatasets persistents currixt dsdims dg'
		in (RLMap.union m m', dg'')
	) spredges (RLMap.empty, dg0)
	in
	Array.fold_right (fun spnnode (m, dg') -> match spnnode with
		| SPRNBranch (_, btask,_,_) ->
			let (mtmp1, dgtmp1) = handleTaskOutput dg' btask
			in
			let (mtmp2, dgtmp2) = handleTaskInput dgtmp1 btask
			in
			(RLMap.union mtmp1 (RLMap.union mtmp2 m), dgtmp2)
		| SPRNJoin _ -> (m, dg')
	) sprnodes (m1, dg1)
| SPRSeq (spr1, spr2) ->
	let (m1, dg1) = findSBPDataSets spr1 dsdescs inpdatasets persistents currixt dsdims dg0
	in
	let (m2, dg2) = findSBPDataSets spr2 dsdescs inpdatasets persistents currixt dsdims dg1
	in
	(RLMap.union m1 m2, dg2)
| SPRPublish _ -> (RLMap.empty, dg0)
;;

let rec (findBPDataSets : anyproc -> datasetdeclaration RLMap.t -> RLSet.t -> RLSet.t -> indextypetype -> indextypetype RLMap.t -> DG.t -> (datasetlocationtype * bool) RLMap.t * DG.t) = fun bproc dsdescs inpdatasets persistents currixt dsdims dg0 -> match bproc with
| PRStop sbproc -> findSBPDataSets sbproc dsdescs inpdatasets persistents currixt dsdims dg0
| PRSeq (spr1, pr2) ->
	let (m1, dg1) = findSBPDataSets spr1 dsdescs inpdatasets persistents currixt dsdims dg0
	in
	let (m2, dg2) = findBPDataSets pr2 dsdescs inpdatasets persistents currixt dsdims dg1
	in
	(RLMap.union m1 m2, dg2)
| PRParal bprocl ->
	List.fold_right (fun pr (m, dg') ->
		let (m', dg'') = findBPDataSets pr dsdescs inpdatasets persistents currixt dsdims dg'
		in (RLMap.union m m', dg'')
	) bprocl (RLMap.empty, dg0)
| PRBranch (btask, tproc, fproc) ->
	let (m1, dg1) = findSBPDataSets (SPRTask btask) dsdescs inpdatasets persistents currixt dsdims dg0
	in
	let (m2, dg2) = findBPDataSets tproc dsdescs inpdatasets persistents currixt dsdims dg1
	in
	let (m3, dg3) = findBPDataSets fproc dsdescs inpdatasets persistents currixt dsdims dg2
	in
	(RLMap.union m1 (RLMap.union m2 m3), dg3)
| PRNetwork (spredges, sprnodes, prends) ->
	let (m1, dg1) = findSBPDataSets (SPRNetwork (spredges, sprnodes)) dsdescs inpdatasets persistents currixt dsdims dg0
	in
	let (m2, dg2) = List.fold_right (fun (_,pr) (m, dg') ->
		let (m', dg'') = findBPDataSets pr dsdescs inpdatasets persistents currixt dsdims dg'
		in (RLMap.union m m', dg'')
	) prends (m1, dg1)
	in
	(RLMap.union m1 m2, dg2)
| PRReplicate (rproc, rprname) ->
	let (AITT aa) = currixt
	in
	let newixt = AITT [| Array.append aa.(0) [| (VInteger, Some rprname) |] |]
	in
	findBPDataSets rproc dsdescs inpdatasets persistents newixt dsdims dg0
;;

let rec combinetwopaths currpath procpath = match currpath, procpath with
| xs, [] -> (xs, 0)
| (x::xs), (None::ys) -> combinetwopaths xs ys
| xs, ((Some y) :: ys) -> let (res,c) = combinetwopaths (y::xs) ys in (res, c+1)
;;

let perslocunion dsname fv1 fv2 =
	let rec sameToPaths l1 l2  = match l1,l2 with
		| [],_ -> []
		| _,[] -> []
		| (x::xs), (y::ys) -> if x = y then x :: (sameToPaths xs ys) else []
	in
	 match fv1,fv2 with
	| None, x -> x
	| x, None -> x
	| Some (path1, upds1), Some (path2, upds2) -> Some ((List.rev (sameToPaths (List.rev path1) (List.rev path2))), List.append upds1 upds2)
;;

let (collectPersistentDatasetsTask : taskdef -> procname list -> procname list RLMap.t -> (procname list * ((taskname * procname list) list)) RLMap.t ) = fun btask currpath foundpers -> match btask with
| UpdateTask (tname, (_,_,taskoutps)) ->
	List.fold_right (fun dsname resm ->
		let (dsorig, dswrites) = try RLMap.find dsname resm with Not_found -> (currpath, [])
		in
		RLMap.add dsname (dsorig, ((tname, currpath) :: dswrites)) resm
	) taskoutps (RLMap.map (fun x -> (x,[])) foundpers)
| _ -> RLMap.map (fun x -> (x,[])) foundpers
;;

let rec (collectPersistentDatasetsSProc : stoppingproc -> procname list -> procname list RLMap.t -> (procname list * ((taskname * procname list) list)) RLMap.t ) = fun sproc currpath foundpers -> match sproc with
| SPRNil -> RLMap.map (fun x -> (x,[])) foundpers
| SPRTask btask -> collectPersistentDatasetsTask btask currpath foundpers
| SPRParal sprocl -> List.fold_right (fun elproc rres -> RLMap.merge perslocunion (collectPersistentDatasetsSProc elproc currpath foundpers) rres) sprocl RLMap.empty
| SPRNetwork (spredges, _) -> Array.fold_right (fun elproc rres -> RLMap.merge perslocunion (collectPersistentDatasetsSProc elproc currpath foundpers) rres) spredges RLMap.empty
| SPRBranch (_, tsproc, fsproc) -> RLMap.merge perslocunion (collectPersistentDatasetsSProc tsproc currpath foundpers) (collectPersistentDatasetsSProc fsproc currpath foundpers)
| SPRSeq (spr1, spr2) ->
	let res1 = collectPersistentDatasetsSProc spr1 currpath foundpers
	in
	let defsonly = RLMap.map (fun (x,_) -> x) res1
	in
    RLMap.merge perslocunion res1 (collectPersistentDatasetsSProc spr2 currpath defsonly)
| SPRPublish _ -> RLMap.map (fun x -> (x,[])) foundpers
;;

(* arguments: 1 - process. 2 - current path. 3 - identified persistent datasets (with paths). Return value: for each persistent dataset, its location, and the locations of its writing tasks (name of the task + path) *)
let rec (collectPersistentDatasetsProc : anyproc -> procname list -> procname list RLMap.t -> (procname list * ((taskname * procname list) list)) RLMap.t ) = fun bproc currpath foundpers -> match bproc with
| PRStop sproc -> collectPersistentDatasetsSProc sproc currpath foundpers
| PRSeq (spr1, pr2) ->
	let res1 = collectPersistentDatasetsSProc spr1 currpath foundpers
	in
	let defsonly = RLMap.map (fun (x,_) -> x) res1
	in
	RLMap.merge perslocunion res1 (collectPersistentDatasetsProc pr2 currpath defsonly)
| PRParal bprocl -> List.fold_right (fun elproc rres -> RLMap.merge perslocunion (collectPersistentDatasetsProc elproc currpath foundpers) rres) bprocl RLMap.empty
| PRNetwork (spredges,_,prends) -> RLMap.merge perslocunion
	(collectPersistentDatasetsSProc (SPRNetwork (spredges, [||])) currpath foundpers)
	(collectPersistentDatasetsProc (PRParal (List.map snd prends)) currpath foundpers)
| PRBranch (_, tproc, fproc) -> RLMap.merge perslocunion (collectPersistentDatasetsProc tproc currpath foundpers) (collectPersistentDatasetsProc fproc currpath foundpers)
| PRReplicate (rproc, rprname) -> collectPersistentDatasetsProc rproc (rprname :: currpath) foundpers
;;

let (setupPersistentsProc : datasetdeclaration RLMap.t -> (procname list * ((taskname * procname list) list)) RLMap.t -> DG.t -> DG.t * persistentdesctype RLMap.t) = fun dssdesc persdesc dg0 ->
	print_endline "Enter setupPersistentsProc";
	let currdg = ref dg0
	in
	let rightside = RLMap.mapi (fun dsname (defpath, updlist) ->
		print_endline ("Consider dataset named " ^ dsname);
		print_endline ("It has the path " ^ (String.concat ":" defpath));
		print_endline ("Its updates are");
		List.iter (fun (taskname,oneupd) ->
			print_endline ("Task " ^ taskname ^ " at path " ^ (String.concat ":" oneupd))
		) updlist;
		let turnPathToDimList path = Array.of_list (List.map (fun s -> (VInteger, Some s)) (List.rev path))
		in
		let dixtcomp0 = turnPathToDimList defpath
		and (_, compdecls) = RLMap.find dsname dssdesc
		in
		let dixtmap = IxM [| Some ((), 0, Array.init (Array.length dixtcomp0) (fun x -> x)) |]
		in
		let isSimpleVariable = 
(*			if ((String.length dsname) >= 5) && ((String.uppercase (String.sub dsname 0 5)) = "STATE") then true else
			if  ((String.length dsname) >= 6) && ((String.uppercase (String.sub dsname 0 6)) = "RECORD") then false else raise (Failure "persistent maps are currently unimplemented")  *)
			if  ((String.length dsname) >= 6) && ((String.uppercase (String.sub dsname 0 6)) = "RECORD") then false else true
		in
		let writingdata = List.fold_right (fun (updtname, updtpath) m ->
			let uixtcomp0 = turnPathToDimList updtpath
			in
			let uixtmap = IxM [| Some ((), 0, Array.init (Array.length uixtcomp0) (fun x -> x)) |]
			in
			let takedimlocs = Array.mapi (fun idx (_, Some idxstr) ->
				let tdnode = {
					nkind = nkTakeDim idxstr VInteger;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = AITT [| uixtcomp0 |];
					outputindextype = AITT [| uixtcomp0 |];
					ixtypemap = uixtmap;
				}
				in
				currdg := DG.addnode tdnode !currdg;
				{l = tdnode.id; t = RLSet.empty}
			) uixtcomp0
			in
			let (dg0, maxloc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) [] (nkMaximum VTimePoint) (fun _ -> raise (Failure "do not call me"))
			in
			currdg := dg0;
			let (dg1, tploc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) (maxloc :: (Array.to_list takedimlocs)) (nkTimePoint updtname (Array.length takedimlocs)) (fun x -> if x = 0 then PortSingle VTimePoint else PortOperInput x)
			in
			currdg := dg1;
			let (dg1a, existloc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) [] nkOr (fun _ -> raise (Failure "do not call me"))
			in
			let (dg1aa, tsixeloc) = GrbInput.addNodesToGraph dg1a (AITT [| uixtcomp0 |]) [] nkOrDT (fun _ -> raise (Failure "do not call me"))
			in
			currdg := dg1aa;
			let updlocs = RLMap.mapi (fun compname comptype ->
				let (dg2, updloc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) [] (nkId comptype) (fun _ -> raise (Failure "do not call me either"))
				in
				currdg := dg2;
				updloc
			) compdecls
			in
			RLMap.add updtname {timepointnode = tploc; updatenode = updlocs; maxnode = maxloc; existnode = existloc; tsixenode = tsixeloc } m
		) updlist RLMap.empty
		in
		let comparenodes = List.fold_right (fun (fstupdtname, fstupdtpath) m ->
			let outercomp0 = turnPathToDimList fstupdtpath
			in
			let outerixtm = IxM [| Some ((), 0, Array.init (Array.length outercomp0) (fun x -> x)) |]
			in
			let innermap = List.fold_right (fun (sndupdtname, sndupdtpath) mm ->
				let innercomp0 = turnPathToDimList sndupdtpath
				in
				let comparecomp0 = Array.append outercomp0 (Array.init ((Array.length innercomp0) - (Array.length dixtcomp0)) (fun i -> innercomp0.(i + (Array.length dixtcomp0))))
				and innerixtm = IxM [| Some ((), 0, Array.init (Array.length innercomp0) (fun x -> if x < (Array.length dixtcomp0) then x else x +  (Array.length outercomp0) - (Array.length dixtcomp0))) |]
				in
				let (dg0, outerWithIdLoc) = GrbInput.putIdNodeOnTop !currdg (RLMap.find fstupdtname writingdata).timepointnode (AITT [| outercomp0 |]) (AITT [| comparecomp0 |]) outerixtm
				in
				let (dg1, innerWithIdLoc) = GrbInput.putIdNodeOnTop dg0 (RLMap.find sndupdtname writingdata).timepointnode (AITT [| innercomp0 |]) (AITT [| comparecomp0 |]) innerixtm
				in
				let (dg2, compareLoc) = GrbInput.addNodesToGraph dg1 (AITT [| comparecomp0 |]) [outerWithIdLoc; innerWithIdLoc] (nkOperation 2 VBoolean OPLessThan) (fun x -> PortOperInput (x+1))
				in
				currdg := dg2;
				RLMap.add sndupdtname compareLoc mm
			) updlist RLMap.empty
			in
			RLMap.add fstupdtname innermap m
		) updlist RLMap.empty
		in
		let forPersWriteOnce = if isSimpleVariable then None else Some (
			let isResettingUpdate updtname = ((String.length updtname) >= 5) && ((String.uppercase (String.sub updtname 0 5)) = "RESET")
			in
			List.fold_right (fun (updtname, updtpath) m ->
				let uixtcomp0 = turnPathToDimList updtpath
				in
				let uixtmap = IxM [| Some ((), 0, Array.init (Array.length uixtcomp0) (fun x -> x)) |]
				in
				let exWLoc = (RLMap.find updtname writingdata).existnode
				in
				let (dg0, isResetLoc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) [] (if isResettingUpdate updtname then nkTrue else nkFalse) (fun _ -> raise (Failure "do not call me either"))
				in
				let (dg1, isSetLoc) = GrbInput.addNodesToGraph dg0 (AITT [| uixtcomp0 |]) [] (if isResettingUpdate updtname then nkFalse else nkTrue) (fun _ -> raise (Failure "do not call me either"))
				in
				let (dg1a, isResetLocDT) = GrbInput.addNodesToGraph dg1 (AITT [| uixtcomp0 |]) [] (if isResettingUpdate updtname then nkTrueDT else nkFalseDT) (fun _ -> raise (Failure "do not call me either"))
				in
				let (dg1b, isSetLocDT) = GrbInput.addNodesToGraph dg1a (AITT [| uixtcomp0 |]) [] (if isResettingUpdate updtname then nkFalseDT else nkTrueDT) (fun _ -> raise (Failure "do not call me either"))
				in
				currdg := dg1b;
				let (outerAndArgs, outerOrArgs) = List.fold_right (fun (w1name, w1path) (ll,kk) ->
					let w1dimlist = turnPathToDimList w1path
					in
					let updw1dimlist = Array.append uixtcomp0 (Array.init ((Array.length w1dimlist) - (Array.length dixtcomp0)) (fun i -> w1dimlist.(i + (Array.length dixtcomp0))))
					and w1ixtm = IxM [| Some ((), 0, Array.init (Array.length w1dimlist) (fun x -> if x < (Array.length dixtcomp0) then x else x +  (Array.length uixtcomp0) - (Array.length dixtcomp0))) |]
					and w1upddimlist = Array.append w1dimlist (Array.init ((Array.length uixtcomp0) - (Array.length dixtcomp0)) (fun i -> uixtcomp0.(i + (Array.length dixtcomp0))))
					in
					let w1swapm = IxM [| Some ((), 0, Array.init (Array.length w1upddimlist) (fun x -> if x < (Array.length dixtcomp0) then x else if x < (Array.length uixtcomp0) then x + (Array.length w1dimlist) - (Array.length dixtcomp0) else x - (Array.length uixtcomp0) + (Array.length dixtcomp0)  ) ) |]
					in
					let (ddg1, isW1SetLoc) = GrbInput.addNodesToGraph !currdg (AITT [| updw1dimlist |]) [] (if isResettingUpdate w1name then nkTrue else nkFalse) (fun _ -> raise (Failure "no calls here"))
					in
					let (ddg1a, isW1ResetLoc) = GrbInput.addNodesToGraph !currdg (AITT [| updw1dimlist |]) [] (if isResettingUpdate w1name then nkFalse else nkTrue) (fun _ -> raise (Failure "no calls here"))
					in
					currdg := ddg1a;
					let (ddgtmp, compww1loc) = (!currdg, RLMap.find w1name (RLMap.find updtname comparenodes))
					in
					let (ddgtmp2, fxw1loc) = GrbInput.putIdNodeOnTop ddgtmp (RLMap.find w1name writingdata).tsixenode (AITT [||]) (AITT [| updw1dimlist |]) w1ixtm
					in
					let (ddgtmp3, nfxw1loc) = GrbInput.addNodesToGraph ddgtmp2 (AITT [| updw1dimlist |]) [fxw1loc] (nkNotFlip true) (fun _ -> PortSingleB false)
					in
					let (ddgtmp4, compw1wloc) = GrbInput.putIdNodeOnTop ddgtmp3 (RLMap.find updtname (RLMap.find w1name comparenodes)) (AITT [||]) (AITT [| updw1dimlist |]) w1swapm
					in 
					let (ddgtmp5, exw1loc) = GrbInput.putIdNodeOnTop ddgtmp (RLMap.find w1name writingdata).existnode (AITT [||]) (AITT [| updw1dimlist |]) w1ixtm
					in
					currdg := ddgtmp5;
					let (innerOrArgs, innerAndArgs) = List.fold_right (fun (w2name, w2path) (lll, kkk) ->
						let w2dimlist = turnPathToDimList w2path
						in
						let updw2dimlist = Array.append updw1dimlist (Array.init ((Array.length w2dimlist) - (Array.length dixtcomp0)) (fun i -> w2dimlist.(i + (Array.length dixtcomp0))))
						in
						let w1w2ixtm = IxM [| Some ((), 0, Array.init ((Array.length w1dimlist) + (Array.length w2dimlist) - (Array.length dixtcomp0)) (fun x -> if x < (Array.length dixtcomp0) then x else x + (Array.length uixtcomp0) - (Array.length dixtcomp0) )) |]
						and w2wixtm = IxM [| Some ((), 0, Array.init ((Array.length uixtcomp0) + (Array.length w2dimlist) - (Array.length dixtcomp0)) (fun x -> if x < (Array.length dixtcomp0) then x else if x < (Array.length w2dimlist) then x + (Array.length uixtcomp0) + (Array.length w1dimlist) - 2 * (Array.length dixtcomp0) else x - (Array.length w2dimlist) + (Array.length dixtcomp0)  )) |]
						and ww1ixtm = IxM [| Some ((), 0, Array.init (Array.length updw1dimlist) (fun x -> x)) |]
						and w2ixtm = IxM [| Some ((), 0, Array.init (Array.length w2dimlist) (fun x -> if x < (Array.length dixtcomp0) then x else x + (Array.length uixtcomp0) + (Array.length w1dimlist) - 2 * (Array.length dixtcomp0))) |]
						and w2w1ixtm = IxM [| Some ((), 0, Array.init ((Array.length w2dimlist) + (Array.length w1dimlist) - (Array.length dixtcomp0)) (fun x -> if x < (Array.length dixtcomp0) then x else if x < (Array.length w2dimlist) then x + (Array.length uixtcomp0) + (Array.length w1dimlist) - 2 * (Array.length dixtcomp0) else x - (Array.length w2dimlist) + (Array.length uixtcomp0)  )) |]
						and ww2ixtm = IxM [| Some ((), 0, Array.init ((Array.length uixtcomp0) + (Array.length w2dimlist) - (Array.length dixtcomp0)) (fun x -> if x < (Array.length uixtcomp0) then x else x + (Array.length w1dimlist) - (Array.length dixtcomp0) )) |]
						in
						let (dddg1, isW2ResetLoc) = GrbInput.addNodesToGraph !currdg (AITT [| updw2dimlist |]) [] (if isResettingUpdate w2name then nkTrue else nkFalse) (fun _ -> raise (Failure "no calls here"))
						in
						let (dddg1a, exW2Loc) = GrbInput.putIdNodeOnTop dddg1 (RLMap.find w2name writingdata).existnode (AITT [||]) (AITT [| updw2dimlist |]) w2ixtm
						in
						let (dddg2, compw1w2Loc) = GrbInput.putIdNodeOnTop dddg1a (RLMap.find w2name (RLMap.find w1name comparenodes)) (AITT [|  |]) (AITT [| updw2dimlist |]) w1w2ixtm
						in
						let (dddg3, compw2wLoc) = GrbInput.putIdNodeOnTop dddg2 (RLMap.find updtname (RLMap.find w2name comparenodes)) (AITT [|  |]) (AITT [| updw2dimlist |]) w2wixtm
						in
						let (dddg4, inmostAndLoc) = GrbInput.addNodesToGraph dddg3 (AITT [| updw2dimlist |]) [isW2ResetLoc; compw1w2Loc; compw2wLoc; exW2Loc] nkAnd (fun _ -> PortStrictB true)
						in
						let (dddg5, isW2SetLoc) = GrbInput.addNodesToGraph dddg4 (AITT [| updw2dimlist |]) [] (if isResettingUpdate w2name then nkFalse else nkTrue) (fun _ -> raise (Failure "no calls here"))
						in
						let (dddg6, exW2LocDT) = GrbInput.putIdNodeOnTop dddg5 (RLMap.find w2name writingdata).tsixenode (AITT [||]) (AITT [| updw2dimlist |]) w2ixtm
						in
						let (dddg7, nexW2Loc) = GrbInput.addNodesToGraph dddg6 (AITT [| updw2dimlist |]) [exW2LocDT] (nkNotFlip true) (fun _ -> PortSingleB false)
						in
						let (dddg8, compw2w1Loc) = GrbInput.putIdNodeOnTop dddg7 (RLMap.find w1name (RLMap.find w2name comparenodes)) (AITT [||]) (AITT [| updw2dimlist |]) w2w1ixtm
						in
						let (dddg9, compww2Loc) = GrbInput.putIdNodeOnTop dddg8 (RLMap.find w2name (RLMap.find updtname comparenodes)) (AITT [||]) (AITT [| updw2dimlist |]) ww2ixtm
						in
						let (dddg10, inmostOrLoc) = GrbInput.addNodesToGraph dddg9 (AITT [| updw2dimlist |]) [isW2SetLoc; nexW2Loc; compw2w1Loc; compww2Loc] nkOr (fun _ -> PortUnstrB true)
						in
						let innerLongOrNode = {
							nkind = nkLongOr;
							id = NewName.get ();
							inputs = PortMap.empty;
							inputindextype = AITT [| updw2dimlist |];
							outputindextype = AITT [| updw1dimlist |];
							ixtypemap = identityIndexMap () (AITT [| updw1dimlist |]);
						}
						and innerLongAndNode = {
							nkind = nkLongAnd;
							id = NewName.get ();
							inputs = PortMap.empty;
							inputindextype = AITT [| updw2dimlist |];
							outputindextype = AITT [| updw1dimlist |];
							ixtypemap = identityIndexMap () (AITT [| updw1dimlist |]);
						}
						in
						currdg := DG.addedge ((identityIndexMap inmostOrLoc.l (AITT [| updw2dimlist |]), NewName.get()), innerLongAndNode.id, PortSingleB true) (DG.addedge ((identityIndexMap inmostAndLoc.l (AITT [| updw2dimlist |]), NewName.get ()), innerLongOrNode.id, PortSingleB true) (DG.addnode innerLongOrNode (DG.addnode innerLongAndNode dddg10)));
						({l = innerLongOrNode.id; t = RLSet.empty} :: lll, {l = innerLongAndNode.id; t = RLSet.empty} :: kkk)
					) updlist ([], [])
					in
					let (ddg2, innerOrLoc) = GrbInput.addNodesToGraph !currdg (AITT [| updw1dimlist |]) (isW1SetLoc :: compww1loc :: nfxw1loc :: innerOrArgs) nkOr (fun _ -> PortUnstrB true)
					in
					let (ddg3, innerAndLoc) = GrbInput.addNodesToGraph ddg2 (AITT [| updw1dimlist |]) (isW1ResetLoc :: exw1loc :: compw1wloc :: innerAndArgs) nkAnd (fun _ -> PortStrictB true)
					in
					let outerLongAndNode = {
						nkind = nkLongAnd;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = AITT [| updw1dimlist |];
						outputindextype = AITT [| uixtcomp0 |];
						ixtypemap = uixtmap;
					}
					and outerLongOrNode = {
						nkind = nkLongOr;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = AITT [| updw1dimlist |];
						outputindextype = AITT [| uixtcomp0 |];
						ixtypemap = uixtmap;
					}
					in
					currdg := DG.addedge ((identityIndexMap innerAndLoc.l (AITT [| updw1dimlist |]), NewName.get ()), outerLongOrNode.id, PortSingleB true) (DG.addedge ((identityIndexMap innerOrLoc.l (AITT [| updw1dimlist |]), NewName.get ()), outerLongAndNode.id, PortSingleB true) (DG.addnode outerLongAndNode (DG.addnode outerLongOrNode ddg3)));
					({l = outerLongAndNode.id; t = RLSet.empty} :: ll, {l = outerLongOrNode.id; t = RLSet.empty} :: kk)
				) updlist ([],[])
				in
				let (dg2, outerAndLoc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) (isSetLoc :: exWLoc :: outerAndArgs) nkAnd (fun _ -> PortStrictB true)
				in
				let (dg3, outerOrLoc) = GrbInput.addNodesToGraph dg2 (AITT [| uixtcomp0 |]) (isResetLoc :: outerOrArgs) nkOr (fun _ -> PortUnstrB true)
				in
				currdg := dg3;
				RLMap.add updtname (outerAndLoc, outerOrLoc) m
			) updlist RLMap.empty
		)
		in
		{
			dataixt = AITT [| dixtcomp0 |];
			updatemode = (match forPersWriteOnce with None -> PersVar | Some locs -> PersWriteOnce locs);
			writings = writingdata;
			writecomparenodes = comparenodes;
		}
	) persdesc
	in
	print_endline "Exit setupPersistentsProc";
	(!currdg, rightside)
;;

let (collectTaskPtrAddresses : taskdef -> procname list -> (procname list * (procname list * int) option) IdtMap.t) = fun btask currpath ->
match btask with
| StartEvent (Some prptr, _) -> IdtMap.singleton prptr (currpath, None)
| StartEvent (None, _) -> IdtMap.empty
| ProcLauncher (_, nprptr, procpath) -> let (res,c) = combinetwopaths currpath procpath in (print_endline ("Process pointer " ^ (NewName.to_string nprptr) ^ " at path " ^ (String.concat ":" currpath) ^ " with procpath = " ^ (String.concat ":" (List.map (function None -> "UP" | Some s -> s) procpath)) ^ " points to the path " ^ (String.concat ":" res) ^ " with indep. number " ^ (string_of_int c)); IdtMap.singleton nprptr (currpath, Some (res, c)))
| _ -> IdtMap.empty
;;

let rec (collectSProcPtrAddresses : stoppingproc -> procname list -> (procname list * (procname list * int) option) IdtMap.t) = fun sproc currpath ->
match sproc with
| SPRNil -> IdtMap.empty
| SPRTask btask -> collectTaskPtrAddresses btask currpath
| SPRParal sprocl -> List.fold_right (fun elproc rres -> IdtMap.union (collectSProcPtrAddresses elproc currpath) rres) sprocl IdtMap.empty
| SPRBranch (_, tsproc, fsproc) -> IdtMap.union (collectSProcPtrAddresses tsproc currpath) (collectSProcPtrAddresses fsproc currpath)
| SPRNetwork (spredges, _) -> Array.fold_right (fun elproc rres -> IdtMap.union (collectSProcPtrAddresses elproc currpath) rres) spredges IdtMap.empty
| SPRSeq (spr1, spr2) -> IdtMap.union (collectSProcPtrAddresses spr1 currpath) (collectSProcPtrAddresses spr2 currpath)
| SPRPublish _ -> IdtMap.empty
;;

let rec (collectProcPtrAddresses : anyproc -> procname list -> (procname list * (procname list * int) option) IdtMap.t) = fun bproc currpath -> (* None indicates, whether this is a StartEvent var *)
match bproc with
| PRStop sproc -> collectSProcPtrAddresses sproc currpath
| PRSeq (spr1, pr2) -> IdtMap.union (collectSProcPtrAddresses spr1 currpath) (collectProcPtrAddresses pr2 currpath)
| PRParal bprocl -> List.fold_right (fun elproc rres -> IdtMap.union (collectProcPtrAddresses elproc currpath) rres) bprocl IdtMap.empty
| PRBranch (_, tproc, fproc) -> IdtMap.union (collectProcPtrAddresses tproc currpath) (collectProcPtrAddresses fproc currpath)
| PRNetwork (spredges,_,prends) ->
	let s1 = collectSProcPtrAddresses (SPRNetwork (spredges, [||])) currpath
	and s2 = collectProcPtrAddresses (PRParal (List.map snd prends)) currpath
	in
	IdtMap.union s1 s2
| PRReplicate (rproc, rprname) -> (print_endline ("collectProcPtrAddresses: entering " ^ rprname); let res = collectProcPtrAddresses rproc (rprname :: currpath) in print_endline ("collectProcPtrAddresses: exiting " ^ rprname); res)
;;

let useDefOfPrPtrs ptrcollection =
	IdtMap.fold (fun dptr (dpath, ddir) (m, backm) ->
		match ddir with
		| None -> (m, backm)
		| Some (spath, _) ->
			IdtMap.fold (fun sptr (spath', beingStart) (mm, backmm) ->
				if beingStart <> None then (mm, backmm) else
				if spath = spath' then
				begin
					let s = try IdtMap.find sptr mm with Not_found -> IdtSet.empty
					in
					(IdtMap.add sptr (IdtSet.add dptr s) mm, IdtMap.add dptr sptr backmm)
				end else (mm, backmm)
			) ptrcollection (m, backm)
	) ptrcollection (IdtMap.empty, IdtMap.empty)
;;

let findBPPrPtrs ptrcollection usedefs defuses dg0 =
	IdtMap.fold (fun dptr (dpath, ddir) (dg1, foundptrs) ->
		print_string ("Now working with proc. pointer " ^ (NewName.to_string dptr)); print_newline ();
		match ddir with
		| None ->
		begin
			let potptrs = try IdtMap.find dptr usedefs with Not_found -> IdtSet.empty
			in
			let (dg2, ll) = IdtSet.fold (fun sptr (dg3, foundptrll) ->
				print_string ("Internally working with proc. pointer " ^ (NewName.to_string sptr)); print_newline ();
				let (spath, Some (_, dindepnum)) = IdtMap.find sptr ptrcollection
				in
				let trunklen = (List.length dpath) - dindepnum
				in
				let sindepnum = (List.length spath) - trunklen
				in
				let currdg = ref dg3
				in
				let revdpath = Array.of_list (List.rev dpath)
				and revspath = Array.of_list (List.rev spath)
				in
				let dixtcomp0 = Array.map (fun s -> (VInteger, Some s)) revdpath
				and sixtcomp0 = Array.map (fun s -> (VInteger, Some s)) revspath
				in
				let dixtypemap = IxM [| Some ((), 0, Array.init (trunklen + dindepnum) (fun x -> x)) |]
				and sixtypemap = IxM [| Some ((), 0, Array.init (trunklen + sindepnum) (fun x -> x)) |]
				in
				let dtakedimnodes = Array.init (trunklen + dindepnum) (fun c ->
					let tdnode = {
						nkind = nkTakeDim (let (_, Some s) = dixtcomp0.(c) in s) VInteger;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = AITT [| dixtcomp0 |];
						outputindextype = AITT [| dixtcomp0 |];
						ixtypemap = dixtypemap;
					}
					in
					currdg := DG.addnode tdnode !currdg;
					tdnode
				)
				and stakedimnodes = Array.init (trunklen + sindepnum) (fun c ->
					let tdnode = {
						nkind = nkTakeDim (let (_, Some s) = sixtcomp0.(c) in s) VInteger;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = AITT [| sixtcomp0 |];
						outputindextype = AITT [| sixtcomp0 |];
						ixtypemap = sixtypemap;
					}
					in
					currdg := DG.addnode tdnode !currdg;
					tdnode
				)
				in
				let addrgennodes = Array.init dindepnum (fun c ->
					let agnode = {
						nkind = nkAddrGen sptr (c + trunklen) (trunklen + sindepnum);
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = AITT [| sixtcomp0 |];
						outputindextype = AITT [| sixtcomp0 |];
						ixtypemap = sixtypemap;
					}
					in
					currdg := DG.addnode agnode !currdg;
					for i = 1 to (trunklen + sindepnum) do
						currdg := DG.addedge ((identityIndexMap stakedimnodes.(i-1).id agnode.inputindextype, NewName.get ()), agnode.id, PortOperInput i) !currdg
					done;
					agnode
				)
				in
				let bixtcomp0 = Array.append sixtcomp0 (Array.sub dixtcomp0 trunklen dindepnum)
				in
				let sToBProjbackmap = Array.init (trunklen + sindepnum) (fun x -> x)
				and dToBProjbackmap = Array.init (trunklen + dindepnum) (fun x -> if x < trunklen then x else x + sindepnum)
				and bixtype = AITT [| bixtcomp0 |]
				in
				let comparisonnodes = Array.init dindepnum (fun c ->
					let compnode = {
						nkind = nkIsEq;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = bixtype;
						outputindextype = bixtype;
						ixtypemap = identityIndexMap () bixtype;
					}
					and incompnode = {
						nkind = nkIsNEq;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = bixtype;
						outputindextype = bixtype;
						ixtypemap = identityIndexMap () bixtype;
					}
					and incompflip = {
						nkind = nkNotFlip false;
						id = NewName.get ();
						inputs = PortMap.empty;
						inputindextype = bixtype;
						outputindextype = bixtype;
						ixtypemap = identityIndexMap () bixtype;
					}
					in
					currdg := DG.addnode incompflip (DG.addnode incompnode (DG.addnode compnode !currdg));
					currdg := DG.addedge ((identityIndexMap addrgennodes.(c).id addrgennodes.(c).outputindextype, NewName.get()), compnode.id, PortCompare) !currdg;
					currdg := DG.addedge ((IxM [| Some (dtakedimnodes.(c + trunklen).id, 0, dToBProjbackmap) |], NewName.get ()), compnode.id, PortCompare) !currdg;
					currdg := DG.addedge ((identityIndexMap addrgennodes.(c).id addrgennodes.(c).outputindextype, NewName.get()), incompnode.id, PortCompare) !currdg;
					currdg := DG.addedge ((IxM [| Some (dtakedimnodes.(c + trunklen).id, 0, dToBProjbackmap) |], NewName.get ()), incompnode.id, PortCompare) !currdg;
					currdg := DG.addedge ((identityIndexMap incompnode.id bixtype, NewName.get ()), incompflip.id, PortSingleB true) !currdg;
					(compnode, incompflip)
				)
				in
				let complocations = Array.to_list (Array.map (fun (n,_) -> {l = n.id; t = RLSet.empty}) comparisonnodes)
				and pmoclocations = Array.to_list (Array.map (fun (_,n) -> {l = n.id; t = RLSet.empty}) comparisonnodes)
				in
				let (dgn, andloc) = GrbInput.addNodesToGraph !currdg (AITT [| bixtcomp0 |]) complocations nkAnd (fun _ -> PortStrictB true)
				in
				let (dgnn, dnaloc) = GrbInput.addNodesToGraph dgn (AITT [| bixtcomp0 |]) pmoclocations nkAndDT (fun _ -> PortUnstrB false)
				in
				(dgnn, ({checknodeid = andloc; kcechnodeid = dnaloc; procpath = spath; numdatadims = sindepnum + trunklen; numjointdims = trunklen; backptr = sptr;} :: foundptrll))
			) potptrs (dg1, [])
			in
			(dg2, IdtMap.add dptr ll foundptrs)
		end
		| Some (spath, sindepnum) ->
		begin
			let trunklen = (List.length spath) - sindepnum
			in
			let dindepnum = (List.length dpath) - trunklen
			in
			let currdg = ref dg1
			in
			let revdpath = Array.of_list (List.rev dpath)
			and revspath = Array.of_list (List.rev spath)
			in
			let dixtcomp0 = Array.map (fun s -> (VInteger, Some s)) revdpath
			and sixtcomp0 = Array.map (fun s -> (VInteger, Some s)) revspath
			in
			let dixtypemap = IxM [| Some ((), 0, Array.init (trunklen + dindepnum) (fun x -> x)) |]
			and sixtypemap = IxM [| Some ((), 0, Array.init (trunklen + sindepnum) (fun x -> x)) |]
			in
			let dtakedimnodes = Array.init (trunklen + dindepnum) (fun c ->
				let tdnode = {
					nkind = nkTakeDim (let (_, Some s) = dixtcomp0.(c) in s) VInteger;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = AITT [| dixtcomp0 |];
					outputindextype = AITT [| dixtcomp0 |];
					ixtypemap = dixtypemap;
				}
				in
				currdg := DG.addnode tdnode !currdg;
				tdnode
			)
			and stakedimnodes = Array.init (trunklen + sindepnum) (fun c ->
				let tdnode = {
					nkind = nkTakeDim (let (_, Some s) = sixtcomp0.(c) in s) VInteger;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = AITT [| sixtcomp0 |];
					outputindextype = AITT [| sixtcomp0 |];
					ixtypemap = sixtypemap;
				}
				in
				currdg := DG.addnode tdnode !currdg;
				tdnode
			)
			in
			let addrgennodes = Array.init sindepnum (fun c ->
				let agnode = {
					nkind = nkAddrGen dptr (c + trunklen) (trunklen + dindepnum);
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = AITT [| dixtcomp0 |];
					outputindextype = AITT [| dixtcomp0 |];
					ixtypemap = dixtypemap;
				}
				in
				currdg := DG.addnode agnode !currdg;
				for i = 1 to (trunklen + dindepnum) do
					currdg := DG.addedge ((identityIndexMap dtakedimnodes.(i-1).id agnode.inputindextype, NewName.get ()), agnode.id, PortOperInput i) !currdg
				done;
				agnode
			)
			in
			let bixtcomp0 = Array.append sixtcomp0 (Array.sub dixtcomp0 trunklen dindepnum)
			in
			let sToBProjbackmap = Array.init (trunklen + sindepnum) (fun x -> x)
			and dToBProjbackmap = Array.init (trunklen + dindepnum) (fun x -> if x < trunklen then x else x + sindepnum)
			and bixtype = AITT [| bixtcomp0 |]
			in
			let comparisonnodes = Array.init sindepnum (fun c ->
				let compnode = {
					nkind = nkIsEq;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = bixtype;
					outputindextype = bixtype;
					ixtypemap = identityIndexMap () bixtype;
				}
				and incompnode = {
					nkind = nkIsNEq;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = bixtype;
					outputindextype = bixtype;
					ixtypemap = identityIndexMap () bixtype;
				}
				and incompflip = {
					nkind = nkNotFlip false;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = bixtype;
					outputindextype = bixtype;
					ixtypemap = identityIndexMap () bixtype;
				}
				in
				currdg := DG.addnode incompflip (DG.addnode incompnode (DG.addnode compnode !currdg));
				currdg := DG.addedge ((IxM [| Some (addrgennodes.(c).id, 0, dToBProjbackmap) |], NewName.get()), compnode.id, PortCompare) !currdg;
				currdg := DG.addedge ((IxM [| Some (stakedimnodes.(c + trunklen).id, 0, sToBProjbackmap) |], NewName.get ()), compnode.id, PortCompare) !currdg;
				currdg := DG.addedge ((IxM [| Some (addrgennodes.(c).id, 0, dToBProjbackmap) |], NewName.get()), incompnode.id, PortCompare) !currdg;
				currdg := DG.addedge ((IxM [| Some (stakedimnodes.(c + trunklen).id, 0, sToBProjbackmap) |], NewName.get ()), incompnode.id, PortCompare) !currdg;
				currdg := DG.addedge ((identityIndexMap incompnode.id bixtype, NewName.get ()), incompflip.id, PortSingleB true) !currdg;
				(compnode, incompflip)
			)
			in
			let complocations = Array.to_list (Array.map (fun (n,_) -> {l = n.id; t = RLSet.empty}) comparisonnodes)
			and pmoclocations = Array.to_list (Array.map (fun (_,n) -> {l = n.id; t = RLSet.empty}) comparisonnodes)
			in
			let (dgn, andloc) = GrbInput.addNodesToGraph !currdg (AITT [| bixtcomp0 |]) complocations nkAnd (fun _ -> PortStrictB true)
			in
			let (dgnn, dnaloc) = GrbInput.addNodesToGraph dgn (AITT [| bixtcomp0 |]) pmoclocations nkAndDT (fun _ -> PortUnstrB false)
			in
			print_string ("The back pointer is ptr no. " ^ (NewName.to_string (IdtMap.find dptr defuses)) ^ "\n");
			(dgnn, IdtMap.add dptr [{checknodeid = andloc; kcechnodeid = dnaloc; procpath = spath; numdatadims = sindepnum + trunklen; numjointdims = trunklen; backptr = IdtMap.find dptr defuses;}] foundptrs)
			(* Used to have "numdatadims = dindepnum + trunklen". Have to see whether the change to "sindepnum" broke something *)
		end
	) ptrcollection (dg0, IdtMap.empty)
;;

let (collectRemoteDataset : IdtSet.t -> datasetname -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * datasetlocationtype) = fun prptr dsname prep dg0 execnode cexenode timenode ->
	let ({dsl_exec = dsexec; dsl_cexe = dscexe; dsl_time = dstime; dsl_attr = dscomplocs; dsl_ixt = (AITT dsixtype)}, isPersistent) = RLMap.find dsname prep.datasets
	and actualptrdescs = List.concat (List.map (fun x -> IdtMap.find x prep.prptrs) (IdtSet.elements prptr))
	in
	if isPersistent then
	begin
		raise (Failure "Persistent datasets are not accessed through process pointers")
	end
	else
	begin
		print_endline ("Collecting remote dataset " ^ dsname ^ " through process pointer(s) " ^ (String.concat ", " (List.map NewName.to_string (IdtSet.elements prptr))));
		print_string ("Current ixtype (cix4p.(0)): ");
		let AITT cix4p = prep.currixt
		in
		Array.iter (fun (vt, mbs) -> let s = match mbs with None -> "NONE" | Some ss -> ss in print_string (s ^ "[" ^ (string_of_valuetype vt) ^ "]; ")) cix4p.(0);
		print_newline ();
		let dsexecnode = DG.findnode dsexec.l dg0
		and dscexenode = DG.findnode dscexe.l dg0
		in
		let (AITT dseb) = dsexecnode.outputindextype
		in
		print_string ("Ixtype of the dataset: ");
		Array.iter (fun (vt, mbs) -> let s = match mbs with None -> "NONE" | Some ss -> ss in print_string (s ^ "[" ^ (string_of_valuetype vt) ^ "]; ")) dseb.(0);
		print_newline ();
		let currdg = ref dg0
		in
		let (llexecs, llcexes, lltimes, llcomps) = List.fold_right (fun oneptrdesc (llexec', llcexe', lltime', llcomp') ->
			print_endline ("Consider ptrdesc with path " ^ (String.concat ":" oneptrdesc.procpath) ^ ", numdatadims = " ^ (string_of_int oneptrdesc.numdatadims) ^ ", numjointdims = " ^ (string_of_int oneptrdesc.numjointdims) ^ ", backptr = " ^ (NewName.to_string oneptrdesc.backptr) );
			let andnode = DG.findnode oneptrdesc.checknodeid.l !currdg
			and dnanode = DG.findnode oneptrdesc.kcechnodeid.l !currdg
			in
			let (AITT anb) = andnode.outputindextype
			in
			print_string ("AND node " ^ (NewName.to_string andnode.id) ^ ", Ixtype of the collectible data (anb.(0)): ");
			Array.iter (fun (vt, mbs) -> let s = match mbs with None -> "NONE" | Some ss -> ss in print_string (s ^ "[" ^ (string_of_valuetype vt) ^ "]; ")) anb.(0);
			print_newline ();
			let dsexecnode = DG.findnode dsexec.l !currdg
			and dscexenode = DG.findnode dscexe.l !currdg
			in
			let (AITT dseb) = dsexecnode.outputindextype
			in
			print_endline ("The dsexecnode is node no. " ^ (NewName.to_string dsexec.l));
			print_string ("Ixtype of the dataset inside the iteration (dseb.(0)): ");
			Array.iter (fun (vt, mbs) -> let s = match mbs with None -> "NONE" | Some ss -> ss in print_string (s ^ "[" ^ (string_of_valuetype vt) ^ "]; ")) dseb.(0);
			print_newline ();
			let projmap_backmap = Array.init oneptrdesc.numdatadims (fun x -> x)
			in
			let projmap = IxM [| Some ((), 0, projmap_backmap) |]
			in
			let numMergedDims = (Array.length anb.(0)) - oneptrdesc.numdatadims + oneptrdesc.numjointdims
			in
			let mergeoit = Array.init numMergedDims (fun x -> if x < oneptrdesc.numjointdims then anb.(0).(x) else anb.(0).(x + oneptrdesc.numdatadims - oneptrdesc.numjointdims))
			and mergeitm = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> if x < oneptrdesc.numjointdims then x else x + oneptrdesc.numdatadims - oneptrdesc.numjointdims)) |]
			and finalprojmap = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> x)) |]
			in
			print_string "Ixtype of the merge result (mergeoit): ";
			Array.iter (fun (vt, mbs) -> let s = match mbs with None -> "NONE" | Some ss -> ss in print_string (s ^ "[" ^ (string_of_valuetype vt) ^ "]; ")) mergeoit;
			print_newline ();
			let goodPtr1 = Array.fold_left (&&) true (Array.mapi (fun idx ixtmem -> ixtmem = anb.(0).(idx)) dseb.(0))
			and goodPtr2 = ((Array.length mergeoit) <= (Array.length cix4p.(0))) && (Array.fold_left (&&) true (Array.mapi (fun idx ixtmem -> ixtmem = cix4p.(0).(idx)) mergeoit))
			in
			if not (goodPtr1 && goodPtr2) then ((None :: llexec'), (None :: llcexe'), (None :: lltime'), (None :: llcomp')) else
			let applyToOneNode nowdg oneloc pnkFilter filterInps pnkLongMerge mergePort checknodeid =
				let (nextdg1, onelochere) = GrbInput.putIdNodeOnTop nowdg oneloc (AITT dsixtype) (AITT anb) (* projmap *) (IxM [| Some ((), 0, Array.init (Array.length dsixtype.(0)) (fun x -> x)) |])
				in
				let vtype = (DG.findnode onelochere.l nextdg1).nkind.outputtype
				in
				let (nextdg2, filterloc) = GrbInput.addNodesToGraph nextdg1 (AITT anb) [checknodeid; onelochere] (pnkFilter vtype) (filterInps vtype) (* TODO: there should be some comparison of process pointers, too. Or, actually... these are done by oneptrdesc.checknodeid... *)
				in
				let mergenode = {
					nkind = pnkLongMerge vtype;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = (AITT anb);
					outputindextype = AITT [| mergeoit |];
					ixtypemap = mergeitm;
				}
				in
				print_endline ("CollectRemoteDataset: created the longMerge node no. " ^ (NewName.to_string mergenode.id));
				let nextdg3 = DG.addedge ((IxM [| Some (filterloc.l, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenode.id, mergePort vtype) (DG.addnode mergenode nextdg2)
				in
				GrbInput.putIdNodeOnTop nextdg3 {l = mergenode.id; t = filterloc.t} (AITT [| mergeoit |]) prep.currixt finalprojmap
			in
			let (dg1, dscomplocshere) = RLMap.fold (fun compname oneloc (nowdg, m) ->
				let (nextdg3, mergeloc) = applyToOneNode nowdg oneloc nkFilter (fun vtype x -> if x = 0 then PortSingleB true else PortSingle vtype) nkLongMerge (fun vtype -> PortSingle vtype) oneptrdesc.checknodeid
				in
				(nextdg3, RLMap.add compname mergeloc m)
			) dscomplocs (!currdg, RLMap.empty)
			in
			let (dg2, dsexechere) = applyToOneNode dg1 dsexec (fun _ -> nkAnd) (fun _ _ -> PortStrictB true) (fun _ -> nkLongOr) (fun _ -> PortSingleB true) oneptrdesc.checknodeid
			in
			let (dg2a, dscexehere) = applyToOneNode dg2 dscexe (fun _ -> nkAndDT) (fun _ _ -> PortUnstrB false) (fun _ -> nkLongOrDT) (fun _ -> PortSingleB false) oneptrdesc.kcechnodeid
			in
			let (dg3, dstimehere) = applyToOneNode dg2a dstime nkFilter (fun vtype x -> if x = 0 then PortSingleB true else PortSingle vtype) nkLongMerge (fun vtype -> PortSingle vtype) oneptrdesc.checknodeid
			in
			(currdg := dg3; ((Some dsexechere :: llexec'), (Some dscexehere :: llcexe'), (Some dstimehere :: lltime'), (Some dscomplocshere :: llcomp')))
		) actualptrdescs ([], [], [], [])
		in
		let mkMergeAndIdNodes inplist isMerge tgtVtype =
			let (dg1, newloc) = addNodesToGraph !currdg prep.currixt inplist (if isMerge then nkMerge tgtVtype else if tgtVtype = VBoolean then nkOr else nkOrDT) (if isMerge then (fun _ -> PortMulti tgtVtype) else (fun _ -> if tgtVtype = VBoolean then PortUnstrB true else PortStrictB false))
			in
			currdg := dg1; newloc
		in
		let rec cleanList = function
			| [] -> []
			| None :: xs -> cleanList xs
			| (Some x) :: xs -> x :: (cleanList xs)
		in
		let resExec = mkMergeAndIdNodes (cleanList llexecs) false VBoolean
		and resCexe = mkMergeAndIdNodes (cleanList llcexes) false VNaeloob
		and resTime = mkMergeAndIdNodes (cleanList lltimes) true VTimePoint
		in
		let (dgf1, resExec') = addNodesToGraph !currdg prep.currixt [resExec; execnode] nkAnd (fun _ -> PortStrictB true)
		in
		let (dgf1a, resCexe') = addNodesToGraph dgf1 prep.currixt [resCexe; cexenode] nkAndDT (fun _ -> PortUnstrB false)
		in
		let (dgf2, resTime') = addNodesToGraph dgf1a prep.currixt [resTime; timenode] (nkMaximum VTimePoint) (fun _ -> PortMulti VTimePoint)
		in
		currdg := dgf2;
		let resComps =
			let clcomps = cleanList llcomps
			and (_, comptypes) = RLMap.find dsname prep.datasetdecls
			in
			RLMap.fold (fun compname oneloc m ->
				let mergetype = RLMap.find compname comptypes
				in
				let mergeloc = mkMergeAndIdNodes (List.map (RLMap.find compname) clcomps) true mergetype
				in
				let (nextdg, filterloc) = GrbInput.addNodesToGraph !currdg prep.currixt [resExec'; mergeloc] (nkFilter mergetype) (fun i -> if i = 0 then PortSingleB true else PortSingle mergetype)
				in
				currdg := nextdg;
				RLMap.add compname filterloc m
			) dscomplocs RLMap.empty
		in
		(!currdg, {dsl_exec = resExec'; dsl_cexe = resCexe'; dsl_time = resTime'; dsl_attr = resComps; dsl_ixt = prep.currixt})
	end
;;

let (collectDataset : IdtSet.t -> datasetname -> taskname -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * datasetlocationtype) = fun maybeprptr dsname tname prep dg0 execnode cexenode timenode -> if not (IdtSet.is_empty maybeprptr) then
	collectRemoteDataset maybeprptr dsname prep dg0 execnode cexenode timenode
else
	let ({dsl_exec = dsexec; dsl_cexe = dscexe; dsl_time = dstime; dsl_attr = dscomplocs; dsl_ixt = (AITT dsixtype)}, isPersistent) = RLMap.find dsname prep.datasets
	and (AITT cixt) = prep.currixt
	in
	if isPersistent then
	begin
		let persdata = RLMap.find dsname prep.persistents
		and (_, dscompdecls) = RLMap.find dsname prep.datasetdecls
		in
		let currdg = ref dg0
		and (AITT dixt) = persdata.dataixt
		in
		let takedims = Array.mapi (fun idx (_, Some idxstr) ->
			let tdnode = {
				nkind = nkTakeDim idxstr VInteger;
				id = NewName.get ();
				inputs = PortMap.empty;
				inputindextype = prep.currixt;
				outputindextype = prep.currixt;
				ixtypemap = identityIndexMap () prep.currixt;
			}
			in
			currdg := DG.addnode tdnode !currdg;
			{l = tdnode.id; t = RLSet.empty}
		) cixt.(0)
		in
		let (dg1, tploc) = GrbInput.addNodesToGraph !currdg prep.currixt (timenode :: (Array.to_list takedims)) (nkTimePoint tname (Array.length takedims)) (fun x -> if x = 0 then PortSingle VTimePoint else PortOperInput x)
		in
		currdg := dg1;
		let cNodes = RLMap.mapi (fun writename perswrec ->
			let tpnode = DG.findnode perswrec.timepointnode.l !currdg
			in
			let AITT tpna = tpnode.outputindextype
			in
			let compnodeixt0 = Array.append cixt.(0) (Array.init ((Array.length tpna.(0)) - (Array.length dixt.(0))) (fun x -> tpna.(0).(x + (Array.length dixt.(0))) ) )
			and ixmToCurrixt = identityIndexMap () prep.currixt
			and ixmToCompNode = IxM [| Some ((), 0, Array.init (Array.length tpna.(0)) (fun x -> if x < Array.length dixt.(0) then x else x + (Array.length cixt.(0)) - (Array.length dixt.(0)) ) ) |]
			in
			let (ddg0, readTimingAtDims) = GrbInput.putIdNodeOnTop !currdg tploc prep.currixt (AITT [| compnodeixt0 |]) ixmToCurrixt
			in
			let (ddg1, writeTimingAtDims) = GrbInput.putIdNodeOnTop ddg0 perswrec.timepointnode tpnode.outputindextype (AITT [| compnodeixt0 |]) ixmToCompNode
			in
			let (ddg2, precompareNodeLoc) = GrbInput.addNodesToGraph ddg1 (AITT [| compnodeixt0 |]) [writeTimingAtDims; readTimingAtDims] (nkOperation 2 VBoolean OPLessThan) (fun x -> PortOperInput (x+1))
			in
			let (ddg2aa, precompareNodeLocOpp) = GrbInput.addNodesToGraph ddg2 (AITT [| compnodeixt0 |]) [readTimingAtDims; writeTimingAtDims] (nkOperation 2 VBoolean OPLessThan) (fun x -> PortOperInput (x+1))
			in
			let (ddg2a, existWriteAtDims) = GrbInput.putIdNodeOnTop ddg2aa perswrec.existnode tpnode.outputindextype (AITT [| compnodeixt0 |]) ixmToCompNode
			in
			let (ddg2b, compareNodeLoc) = GrbInput.addNodesToGraph ddg2a (AITT [| compnodeixt0 |]) [precompareNodeLoc; existWriteAtDims] nkAnd (fun _ -> PortStrictB true)
			in
			let (ddg2c, compareNodeLocOpp) = GrbInput.addNodesToGraph ddg2b (AITT [| compnodeixt0 |]) [precompareNodeLocOpp; existWriteAtDims] nkAnd (fun _ -> PortStrictB true)
			in
			currdg := ddg2c;
			match persdata.updatemode with
				| PersVar -> (compareNodeLoc, compareNodeLocOpp, tpna.(0), compnodeixt0, ixmToCurrixt, ixmToCompNode)
				| PersWriteOnce mm ->
				begin
					let (rasloc, notrasloc) = RLMap.find writename mm
					in
					let (ddg3, rasLocAtDims) = GrbInput.putIdNodeOnTop ddg2 rasloc tpnode.outputindextype (AITT [| compnodeixt0 |]) ixmToCompNode
					in
					let (ddg4, realCLoc) = GrbInput.addNodesToGraph ddg3 (AITT [| compnodeixt0 |]) [rasLocAtDims; compareNodeLoc] nkAnd (fun _ -> PortStrictB true)
					in
					let (ddg5, realGLoc) = GrbInput.addNodesToGraph ddg4 (AITT [| compnodeixt0 |]) [rasLocAtDims; compareNodeLocOpp] nkAnd (fun _ -> PortStrictB true)
					in
					currdg := ddg5;
					(realCLoc, realGLoc, tpna.(0), compnodeixt0, ixmToCurrixt, ixmToCompNode)
				end
		) persdata.writings
		in
		let filterConditions = RLMap.mapi (fun writename (cNodeLoc, gNodeLoc, writecomp0, rwcomp0, mtoread, mtowrite) ->
			let ornodeArgLocs = RLMap.fold (fun write2name (cNode2Loc, gNode2Loc, write2comp0, rw2comp0, m2toread, m2towrite) ll ->
				let w2wcomploc = RLMap.find writename (RLMap.find write2name persdata.writecomparenodes)
				and fw2loc = (RLMap.find write2name persdata.writings).tsixenode
				in
				let allcomp0 = Array.append rw2comp0 (Array.init ((Array.length rwcomp0) - (Array.length cixt.(0))) (fun x -> rwcomp0.(x + (Array.length cixt.(0))) ))
				and malltow2wcomp = IxM [| Some ((), 0, Array.init ((Array.length rw2comp0) + (Array.length rwcomp0) - 2 * (Array.length cixt.(0)) + (Array.length dixt.(0))) (fun x -> if x < Array.length dixt.(0) then x else x + (Array.length cixt.(0)) - (Array.length dixt.(0))  ) ) |]
				and malltowname = IxM [| Some ((), 0, Array.init (Array.length rwcomp0) (fun x -> if x < Array.length cixt.(0) then x else x + (Array.length rw2comp0) - (Array.length cixt.(0)) ) ) |]
				and malltow2name = IxM [| Some ((), 0, Array.init (Array.length rw2comp0) (fun x -> x) ) |]
				in
				let (dddg1, gNode2LocAtDims) = GrbInput.putIdNodeOnTop !currdg gNode2Loc (AITT [||]) (AITT [| allcomp0 |]) malltow2name
				in
				let (dddg2, compLocAtDims) = GrbInput.putIdNodeOnTop dddg1 w2wcomploc (AITT [||]) (AITT [| allcomp0 |]) malltow2wcomp
				in
				let (dddg2apre, fw2LocAtPreDims) = GrbInput.putIdNodeOnTop dddg2 fw2loc (AITT [|write2comp0 |]) (AITT [| rw2comp0 |]) m2towrite
				in
				let (dddg2a, fw2LocAtDims) = GrbInput.putIdNodeOnTop dddg2apre fw2LocAtPreDims (AITT [|rw2comp0 |]) (AITT [| allcomp0 |]) malltow2name
				in
				let (dddg3, notCompLoc) = GrbInput.addNodesToGraph dddg2a (AITT [| allcomp0 |]) [fw2LocAtDims] (nkNotFlip true) (fun _ -> PortSingleB false)
				in
				let (dddg4, innerOrLoc) = GrbInput.addNodesToGraph dddg3 (AITT [| allcomp0 |]) [notCompLoc; gNode2LocAtDims; compLocAtDims] nkOr (fun _ -> PortUnstrB true)
				in
				let longAndNode = {
					nkind = nkLongAnd;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = AITT [| allcomp0 |];
					outputindextype = AITT [| rwcomp0 |];
					ixtypemap = malltowname;
				}
				in
				currdg := DG.addedge ((identityIndexMap innerOrLoc.l (AITT [| allcomp0 |]), NewName.get ()), longAndNode.id, PortSingleB true) (DG.addnode longAndNode dddg4);
				{l = longAndNode.id; t = innerOrLoc.t} :: ll
			) cNodes []
			in
			let (ddg1, andNLoc) = GrbInput.addNodesToGraph !currdg (AITT [| rwcomp0 |]) (cNodeLoc :: ornodeArgLocs) nkAnd (fun _ -> PortStrictB true)
			in
			currdg := ddg1;
			andNLoc
		) cNodes
		in
		let dscomplocs' = RLMap.mapi (fun compname comptype ->
			let longMergeLocs = RLMap.fold (fun writename (cNodeLoc, _, writecomp0, rwcomp0, mtoread, mtowrite) ll ->
				let fcondLoc = RLMap.find writename filterConditions
				and valLoc = RLMap.find compname (RLMap.find writename persdata.writings).updatenode
				in
				let (ddg0, valAtDims) = GrbInput.putIdNodeOnTop !currdg valLoc (AITT [||]) (AITT [| rwcomp0 |]) mtowrite
				in
				let (ddg1, filterLoc) = GrbInput.addNodesToGraph ddg0 (AITT [| rwcomp0 |]) [fcondLoc;valAtDims] (nkFilter comptype) (fun x -> if x = 0 then PortSingleB true else PortSingle comptype)
				in
				let lmergenode = {
					nkind = nkLongMerge comptype;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = AITT [| rwcomp0 |];
					outputindextype = prep.currixt;
					ixtypemap = mtoread;
				}
				in
				currdg := DG.addedge ((identityIndexMap filterLoc.l (AITT [| rwcomp0 |]), NewName.get ()), lmergenode.id, PortSingle comptype) (DG.addnode lmergenode ddg1);
				{l = lmergenode.id; t = filterLoc.t} :: ll
			) cNodes []
			in
			let (dg1, mergeloc) = GrbInput.addNodesToGraph !currdg prep.currixt longMergeLocs (nkMerge comptype) (fun _ -> PortMulti comptype)
			in
			currdg := dg1;
			mergeloc
		) dscompdecls
		in
		(!currdg, {dsl_exec = execnode; dsl_cexe = cexenode; dsl_time = tploc; dsl_attr = dscomplocs'; dsl_ixt = prep.currixt})
	end
	else
	begin
		let projmap = IxM [| Some ((), 0, Array.init (Array.length dsixtype.(0)) (fun x -> x) ) |]
		in
		let (dg1, dsexec') = GrbInput.putIdNodeOnTop dg0 dsexec (AITT dsixtype) prep.currixt projmap
		in
		let (dg1a, dscexe') = GrbInput.putIdNodeOnTop dg1 dscexe (AITT dsixtype) prep.currixt projmap
		in
		let (dg2, dstime') = GrbInput.putIdNodeOnTop dg1a dstime (AITT dsixtype) prep.currixt projmap
		in
		let (dg3, dscomplocs') = RLMap.fold (fun compname oneloc (dg', m) ->
			let (dg'', oneloc') = GrbInput.putIdNodeOnTop dg' oneloc (AITT dsixtype) prep.currixt projmap
			in
			(dg'', RLMap.add compname oneloc' m)
		) dscomplocs (dg2, RLMap.empty)
		in
		let (dg4, dsexec'') = GrbInput.addNodesToGraph dg3 prep.currixt [dsexec'; execnode] nkAnd (fun _ -> PortStrictB true)
		in
		let (dg4a, dscexe'') = GrbInput.addNodesToGraph dg4 prep.currixt [dscexe'; cexenode] nkAndDT (fun _ -> PortUnstrB false)
		in
		let (dg5, dstime'') = GrbInput.addNodesToGraph dg4a prep.currixt [dstime'; timenode] (nkMaximum VTimePoint) (fun _ -> PortMulti VTimePoint)
		in
		(dg5, {dsl_exec = dsexec''; dsl_cexe = dscexe''; dsl_time = dstime''; dsl_attr = dscomplocs'; dsl_ixt = prep.currixt})
	end
;;

let (writeDataSet : taskname -> datasetname -> graphpreparationtype -> DG.t -> datasetlocationtype -> DG.t * (GrbInput.attrlocationtype option)) = fun tname dsname prep dg0 {dsl_exec = dsexecwr; dsl_cexe = dscexewr; dsl_time = dstimewr; dsl_attr = dscolswr} ->
	let ({dsl_exec = dsexec; dsl_cexe = dscexe; dsl_time = dstime; dsl_attr = dscomplocs; dsl_ixt = (AITT dsixtype)}, isPersistent) = RLMap.find dsname prep.datasets
	in
	let (AITT ixt) = prep.currixt
	in
	let backmap = Array.init (Array.length ixt.(0)) (fun x -> x)
	in
	if isPersistent then
	begin
		let persdata = RLMap.find dsname prep.persistents
		in
		let perspointdata = RLMap.find tname persdata.writings
		in
		let dg1 = DG.addedge ((IxM [| Some (dscexewr.l, 0, backmap) |], NewName.get ()), perspointdata.tsixenode.l, PortStrictB false) (DG.addedge ((IxM [| Some (dsexecwr.l, 0, backmap) |], NewName.get ()), perspointdata.existnode.l, PortUnstrB true) (DG.addedge ((IxM [| Some (dstimewr.l, 0, backmap) |], NewName.get ()), perspointdata.maxnode.l, PortMulti VTimePoint) dg0))
		in
		let dg2 = RLMap.fold (fun compname onelocwr dg' ->
			let oneloc = RLMap.find compname perspointdata.updatenode
			in
			let vtype = (DG.findnode oneloc.l dg').nkind.outputtype
			in
			DG.addedge ((IxM [| Some (onelocwr.l, 0, backmap) |], NewName.get ()), oneloc.l, PortSingle vtype) dg'
		) dscolswr dg1
		in
		(dg2, Some perspointdata.timepointnode)
	end
	else
	begin
		let dg1 = DG.addedge ((IxM [| Some (dscexewr.l, 0, backmap) |], NewName.get ()), dscexe.l, PortStrictB false) (DG.addedge ((IxM [| Some (dsexecwr.l, 0, backmap) |], NewName.get ()), dsexec.l, PortUnstrB true) dg0)
		in
		let dg2 = DG.addedge ((IxM [| Some (dstimewr.l, 0, backmap) |], NewName.get ()), dstime.l, PortMulti VTimePoint) dg1
		in
		let dg3 = RLMap.fold (fun compname onelocwr dg' ->
			let oneloc = RLMap.find compname dscomplocs
			in
			let vtype = (DG.findnode oneloc.l dg').nkind.outputtype
			in
			DG.addedge ((IxM [| Some (onelocwr.l, 0, backmap) |], NewName.get ()), oneloc.l, PortMulti vtype) dg'
		) dscolswr dg2
		in
		(dg3, None)
	end
;;

let rec (convertDExpr : definingexpr -> graphpreparationtype -> bool -> DG.t -> datasetlocationtype RLMap.t -> DG.t * GrbInput.attrlocationtype) = fun dexpr prep isGuard dg0 inpdatasets ->
let convertGeneric fname arglist =
	if fname = "equals" then Some (DEOp (OPIsEq, arglist))
	else None
in
match dexpr with
| DEVar (dsname, dscomp) ->
	let {dsl_attr = dslocs} = RLMap.find dsname inpdatasets
	in
	(dg0, RLMap.find dscomp dslocs)
| DEAppl (fname, arglist) ->
	let perhapsMeaningful = convertGeneric fname arglist
	in
	(match perhapsMeaningful with
		| None ->
			let (dg1, argloclist) = List.fold_right (fun dexpr' (dg', foundloclist) ->
				let (dg'', nextloc) = convertDExpr dexpr' prep false dg' inpdatasets
				in
				(dg'', (nextloc :: foundloclist))
			) arglist (dg0, [])
			in
			GrbInput.addNodesToGraph dg1 prep.currixt argloclist (nkGeneric fname (isGuard || (((String.length fname) >= 3) && ((String.sub fname 0 3) = "is_"))) (List.length argloclist)) (fun x -> PortOperInput (x+1))
		| Some altExpr -> convertDExpr altExpr prep isGuard dg0 inpdatasets
	)
| DEOp (op, arglist) ->
	let (dg1, argloclist) = List.fold_right (fun dexpr' (dg', foundloclist) ->
		let (dg'', nextloc) = convertDExpr dexpr' prep false dg' inpdatasets
		in
		(dg'', (nextloc :: foundloclist))
	) arglist (dg0, [])
	in
	GrbInput.addNodesToGraph dg1 prep.currixt argloclist (nkOperation (List.length arglist) (if isGuard then VBoolean else VAny) op) (fun x -> PortOperInput (x+1))
| DEIntConst x ->
	GrbInput.addNodesToGraph dg0 prep.currixt [] (nkOperation 0 VInteger (OPIntConst x)) (fun _ -> PortSingle VInteger)
| DEFloatConst x ->
	GrbInput.addNodesToGraph dg0 prep.currixt [] (nkOperation 0 VReal (OPRealConst x)) (fun _ -> PortSingle VReal)
| DEStringConst x ->
	GrbInput.addNodesToGraph dg0 prep.currixt [] (nkOperation 0 VString (OPStringConst x)) (fun _ -> PortSingle VString)
| DEPtrSrcCheck (prptr, procpathorbackptr) ->
	let (AITT xa) = prep.currixt
	in
	let checkptrpoint ptrpoint = match procpathorbackptr with
		| Left procpath ->
			let mypath = List.rev (Array.to_list (Array.map (fun (_, Some s) -> s) xa.(0)))
			in
			let (qpath,_) = combinetwopaths mypath procpath
			in
			qpath = ptrpoint.procpath
		| Right backpointer -> backpointer = ptrpoint.backptr
	in
	let ptrdesc = IdtMap.find prptr prep.prptrs
	in
	let (dg1, locchecks) = List.fold_right (fun ptrpoint (dg', ll) ->
		if checkptrpoint ptrpoint then
		begin
			let andnode = DG.findnode ptrpoint.checknodeid.l dg'
			in
			let (AITT anb) = andnode.outputindextype
			in
			let projmap = IxM [| Some ((), 0, Array.init ptrpoint.numdatadims (fun x -> x)) |]
			in
			let numMergedDims = (Array.length anb.(0)) - ptrpoint.numdatadims + ptrpoint.numjointdims
			in
			let mergeoit = AITT [| Array.init numMergedDims (fun x -> if x < ptrpoint.numjointdims then anb.(0).(x) else anb.(0).(x + ptrpoint.numdatadims - ptrpoint.numjointdims)) |]
			and mergeitm = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> if x < ptrpoint.numjointdims then x else x + ptrpoint.numdatadims - ptrpoint.numjointdims)) |]
			in
			let mergenode = {
				nkind = nkLongOr;
				id = NewName.get ();
				inputs = PortMap.empty;
				inputindextype = (AITT anb);
				outputindextype = mergeoit;
				ixtypemap = mergeitm;
			}
			in
			let nextdg3 = DG.addedge ((IxM [| Some (andnode.id, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenode.id, PortSingleB true) (DG.addnode mergenode dg')
			in
			let finalprojmap = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> x)) |]
			in
			let (dg'', projloc) = GrbInput.putIdNodeOnTop nextdg3 {l = mergenode.id; t = RLSet.empty} mergeoit prep.currixt finalprojmap
			in (dg'', projloc :: ll)
		end else (dg', ll)
	) ptrdesc (dg0, [])
	in
	GrbInput.addNodesToGraph dg1 prep.currixt locchecks nkOr (fun _ -> PortUnstrB true)
;;

let (convertTask : taskdef -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * ((GrbInput.attrlocationtype * GrbInput.attrlocationtype, GrbInput.attrlocationtype * GrbInput.attrlocationtype * GrbInput.attrlocationtype * GrbInput.attrlocationtype) either) * GrbInput.attrlocationtype) = fun btask prep dg0 execnode cexenode timenode -> match btask with
| NormalTask (tname, (_, proginps, _))
| UpdateTask (tname, (_, proginps, _))
| GuardTask (tname, _, proginps) ->
	let (prog, isGuard, progouts) = (match btask with NormalTask (_, (p,_,po)) | UpdateTask (_, (p,_,po)) -> (p, false, po) | GuardTask (_,s,_) -> ([(("",""),s)], true, []) )
	and isUpdate = (match btask with UpdateTask _ -> true | _ -> false)
	in
	let (dg1, inpdatasets) = List.fold_right (fun (pptropt, dsname) (dg', m) ->
		let (dg'', dsloc) = collectDataset pptropt dsname tname prep dg' execnode cexenode timenode
		in
		(dg'', RLMap.add dsname dsloc m)
	) proginps (dg0, RLMap.empty)
	in
	let (dg2, outps) = List.fold_right (fun ((newdsname, newcompname), defexpr) (dg', computedthings) ->
		let (dg'', compattr) = convertDExpr defexpr prep isGuard dg' inpdatasets
		in
		let currds = try RLMap.find newdsname computedthings with Not_found -> RLMap.empty
		in
		(dg'', RLMap.add newdsname (RLMap.add newcompname compattr currds) computedthings)
	) prog (dg1, RLMap.empty)
	in
	let (execnodelist, cexenodelist, timenodelist) = RLMap.fold (fun _ {dsl_exec = dsexec; dsl_cexe = dscexe; dsl_time = dstime} (l1,l2,l3) ->
		((dsexec :: l1), (dscexe :: l2), (dstime :: l3))
	) inpdatasets ([execnode], [cexenode], [timenode])
	in
	let (dg3, allexec) = GrbInput.addNodesToGraph dg2 prep.currixt execnodelist nkAnd (fun _ -> PortStrictB true)
	in
	let (dg3a, allcexe) = GrbInput.addNodesToGraph dg3 prep.currixt cexenodelist nkAndDT (fun _ -> PortUnstrB false)
	in
	let (dg4, alltime) = GrbInput.addNodesToGraph dg3a prep.currixt timenodelist (nkMaximum VTimePoint) (fun _ -> PortMulti VTimePoint)
	in
	if isGuard then
	begin
		let guardloc = RLMap.find "" (RLMap.find "" outps)
		in
		let (dg5, posguard) = GrbInput.addNodesToGraph dg4 prep.currixt [allexec; guardloc] nkAnd (fun _ -> PortStrictB true)
		in
		let (dg6, notguardloc) = GrbInput.addNodesToGraph dg5 prep.currixt [guardloc] nkNot (fun _ -> PortUSingleB)
		in
		let (dg7, negguard) = GrbInput.addNodesToGraph dg6 prep.currixt [allexec; notguardloc] nkAnd (fun _ -> PortStrictB true)
		in
		let (dg8, preposGuardDT) = GrbInput.addNodesToGraph dg7 prep.currixt [notguardloc] (nkNotFlip false) (fun _ -> PortSingleB true)
		in
		let (dg9, prenegGuardDT) = GrbInput.addNodesToGraph dg8 prep.currixt [guardloc] (nkNotFlip false) (fun _ -> PortSingleB true)
		in
		let (dg10, posGuardDT) = GrbInput.addNodesToGraph dg9 prep.currixt [preposGuardDT; allcexe] nkAndDT (fun _ -> PortUnstrB false)
		in
		let (dg11, negGuardDT) = GrbInput.addNodesToGraph dg10 prep.currixt [prenegGuardDT; allcexe] nkAndDT (fun _ -> PortUnstrB false)
		in
		(dg11, Right (posguard, posGuardDT, negguard, negGuardDT), alltime)
	end
	else
	begin
		let (dg5, newtimes) = RLMap.fold (fun newdsname newdslocs (dg', timell) ->
			let (dg'', posstimeloc) = writeDataSet tname newdsname prep dg' {dsl_exec = allexec; dsl_cexe = allcexe; dsl_time = alltime; dsl_attr = newdslocs; dsl_ixt = prep.currixt}
			in
			match posstimeloc with
			| None -> (dg'', timell)
			| Some realtimeloc -> (dg'', realtimeloc :: timell)
		) outps (dg4, [])
		in
		let (dg6, alltime') = if newtimes = [] then (dg5, alltime) else GrbInput.addNodesToGraph dg5 prep.currixt (alltime :: newtimes) (nkMaximum VTimePoint) (fun x -> PortMulti VTimePoint)
		in
		(dg6, Left (allexec, allcexe), alltime')
	end
| StartEvent (Some prptr, tname) ->
	let prptrdescl = IdtMap.find prptr prep.prptrs
	in
	let (dg1, locchecks, locchecksDT) = List.fold_right (fun ptrpoint (dg', ll, kk) ->
		let andnode = DG.findnode ptrpoint.checknodeid.l dg'
		and andnodeDT = DG.findnode ptrpoint.kcechnodeid.l dg'
		in
		let (AITT anb) = andnode.outputindextype
		in
		let projmap = IxM [| Some ((), 0, Array.init ptrpoint.numdatadims (fun x -> x)) |]
		in
		let numMergedDims = (Array.length anb.(0)) - ptrpoint.numdatadims + ptrpoint.numjointdims
		in
		let mergeoit = AITT [| Array.init numMergedDims (fun x -> if x < ptrpoint.numjointdims then anb.(0).(x) else anb.(0).(x + ptrpoint.numdatadims - ptrpoint.numjointdims)) |]
		and mergeitm = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> if x < ptrpoint.numjointdims then x else x + ptrpoint.numdatadims - ptrpoint.numjointdims)) |]
		in
		let mergenode = {
			nkind = nkLongOr;
			id = NewName.get ();
			inputs = PortMap.empty;
			inputindextype = (AITT anb);
			outputindextype = mergeoit;
			ixtypemap = mergeitm;
		}
		and mergenodeDT = {
			nkind = nkLongOrDT;
			id = NewName.get ();
			inputs = PortMap.empty;
			inputindextype = (AITT anb);
			outputindextype = mergeoit;
			ixtypemap = mergeitm;
		}
		in
		let nextdg3 = DG.addedge ((IxM [| Some (andnodeDT.id, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenodeDT.id, PortSingleB false) (DG.addedge ((IxM [| Some (andnode.id, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenode.id, PortSingleB true) (DG.addnode mergenode (DG.addnode mergenodeDT dg')))
		in
		let finalprojmap = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> x)) |]
		in
		let (dg'', projloc) = GrbInput.putIdNodeOnTop nextdg3 {l = mergenode.id; t = RLSet.empty} mergeoit prep.currixt finalprojmap
		in
		let (dgthird, projlocDT) = GrbInput.putIdNodeOnTop dg'' {l = mergenodeDT.id; t = RLSet.empty} mergeoit prep.currixt finalprojmap
		in (dgthird, projloc :: ll, projlocDT :: kk)
	) prptrdescl (dg0, [], [])
	in
	let (dg2, ornodeloc) = GrbInput.addNodesToGraph dg1 prep.currixt locchecks nkOr (fun _ -> PortUnstrB true)
	in
	let (dg3, startnodeloc) = GrbInput.addNodesToGraph dg2 prep.currixt [ornodeloc; execnode] nkAnd (fun _ -> PortStrictB true)
	in
	let (dg4, ornodelocDT) = GrbInput.addNodesToGraph dg3 prep.currixt locchecksDT nkOrDT (fun _ -> PortStrictB false)
	in
	let (dg5, snlDT) = GrbInput.addNodesToGraph dg4 prep.currixt [ornodelocDT; cexenode] nkAndDT (fun _ -> PortUnstrB false)
	in
	(dg5, Left (startnodeloc, snlDT), timenode)
| StartEvent (None, tname) ->
	let (dg1, invokenodeloc) = GrbInput.addNodesToGraph dg0 prep.currixt [] (nkInputExists tname) (fun _ -> PortSingleB true)
	in
	let (dg2, startnodeloc) = GrbInput.addNodesToGraph dg1 prep.currixt [execnode; invokenodeloc] nkAnd (fun _ -> PortStrictB true)
	in
	let (dg3, noInvokeNodeLoc) = GrbInput.addNodesToGraph dg2 prep.currixt [invokenodeloc] nkNot (fun _ -> PortUSingleB)
	in
	let (dg4, invokenodelocDT) = GrbInput.addNodesToGraph dg3 prep.currixt [noInvokeNodeLoc] (nkNotFlip false) (fun _ -> PortSingleB true)
	in
	let (dg5, snlDT) = GrbInput.addNodesToGraph dg4 prep.currixt [cexenode; invokenodelocDT] nkAndDT (fun _ -> PortUnstrB false)
	in
	(dg5, Left (startnodeloc, snlDT), timenode)
| ProcLauncher (tname, prptr, launchpath) ->
	let AITT cixt = prep.currixt
	in
	let mypath = List.rev (Array.to_list (Array.map (fun (_, Some s) -> s) cixt.(0)))
	in
	let (lpath,_) = combinetwopaths mypath launchpath
	in
	let prptrdesc = List.hd (IdtMap.find prptr prep.prptrs)
	in
	let backptrdescl = IdtMap.find prptrdesc.backptr prep.prptrs
	in
	let backptrdesc = List.find (fun st -> st.backptr = prptr) backptrdescl
	in
	let projmap = IxM [| Some (execnode.l, 0, Array.init (Array.length cixt.(0)) (fun x -> x)) |]
	and projmapDT = IxM [| Some (cexenode.l, 0, Array.init (Array.length cixt.(0)) (fun x -> x)) |]
	in
	let dg1 = DG.addedge ((projmapDT, NewName.get ()), backptrdesc.kcechnodeid.l, PortUnstrB false) (DG.addedge ((projmap, NewName.get ()), backptrdesc.checknodeid.l, PortStrictB true) dg0)
	in
	(dg1, Left (execnode, cexenode), timenode)
;;

let rec (convertStoppingProcWork : stoppingproc -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * GrbInput.attrlocationtype * GrbInput.attrlocationtype * GrbInput.attrlocationtype) = fun bproc prep currdg execnode cexenode timenode -> match bproc with
| SPRNil -> (currdg, execnode, cexenode, timenode)
| SPRTask taskdesc ->
	let (dg0, Left (execnode', cexenode'), timenode') = convertTask taskdesc prep currdg execnode cexenode timenode
	in
	(dg0, execnode', cexenode', timenode')
| SPRParal sprlist -> if sprlist = [] then (currdg, execnode, cexenode, timenode) else
	let (dg0, exnlist, cenlist, timlist) = List.fold_right (fun prx (dg, exl, cel, tml) ->
		let (dg', exn', cen', tmn') = convertStoppingProcWork prx {prep with atprocstart = false} dg execnode cexenode timenode
		in (dg', (exn' :: exl), (cen' :: cel), (tmn' :: tml))
	) sprlist (currdg, [], [], [])
	in
	let (dg1, nexecnode) = GrbInput.addNodesToGraph dg0 prep.currixt exnlist nkAnd (fun _ -> PortStrictB true)
	in
	let (dg1a, ncexenode) = GrbInput.addNodesToGraph dg1 prep.currixt cenlist nkAndDT (fun _ -> PortUnstrB false)
	in
	let (dg2, ntimenode) = GrbInput.addNodesToGraph dg1a prep.currixt timlist (nkMaximum VTimePoint) (fun _ -> PortMulti VTimePoint)
	in
	(dg2, nexecnode, ncexenode, ntimenode)
| SPRBranch (booltask, truebranch, falsebranch) ->
	let (dg0, Right (exectrue, cexetrue, execfalse, cexefalse), timenode') = convertTask booltask {prep with atprocstart = false} currdg execnode cexenode timenode
	in
	let (dg1, execaftertrue, cexeaftertrue, timeaftertrue) = convertStoppingProcWork truebranch {prep with atprocstart = false} dg0 exectrue cexetrue timenode'
	in
	let (dg2, execafterfalse, cexeafterfalse, timeafterfalse) = convertStoppingProcWork falsebranch {prep with atprocstart = false} dg1 execfalse cexefalse timenode'
	in
	let (dg3, execafter) = GrbInput.addNodesToGraph dg2 prep.currixt [execaftertrue; execafterfalse] nkOr (fun _ -> PortUnstrB true)
	in
	let (dg3a, cexeafter) = GrbInput.addNodesToGraph dg3 prep.currixt [cexeaftertrue; cexeafterfalse] nkOrDT (fun _ -> PortStrictB false)
	in
	let (dg3b, filtertruetime) = GrbInput.addNodesToGraph dg3a prep.currixt [execaftertrue; timeaftertrue] (nkFilter VTimePoint) (fun x -> if x = 0 then PortSingleB true else PortSingle VTimePoint)
	in
	let (dg3c, filterfalsetime) = GrbInput.addNodesToGraph dg3b prep.currixt [execafterfalse; timeafterfalse] (nkFilter VTimePoint) (fun x -> if x = 0 then PortSingleB true else PortSingle VTimePoint)
	in
	let (dg4, timeafter) = GrbInput.addNodesToGraph dg3c prep.currixt [filtertruetime; filterfalsetime] (nkMerge VTimePoint) (fun _ -> PortMulti VTimePoint)
	in
	(dg4, execafter, cexeafter, timeafter)
| SPRNetwork (spredges, sprnodes) ->
	let lastidx = (Array.length spredges)
	in
	let (dgres, allends) = convertStoppingProcNetwork spredges sprnodes prep currdg execnode cexenode timenode
	in
	let (execlast, cexelast, timelast) = allends.(lastidx)
	in
	(dgres, execlast, cexelast, timelast)
| SPRSeq (pr1, pr2) ->
	 let (dg1,exn1, cen1, tim1) = convertStoppingProcWork pr1 prep currdg execnode cexenode timenode
	 in
	 convertStoppingProcWork pr2 {prep with atprocstart = false} dg1 exn1 cen1 tim1
| SPRPublish (prptropt, dataname) ->
		let (dg0, {dsl_exec = dsexec; dsl_time = dstime; dsl_attr = dsloc}) = collectDataset (match prptropt with None -> IdtSet.empty | Some prptr -> IdtSet.singleton prptr) dataname ("Publish " ^ dataname) prep currdg execnode cexenode timenode
		in
		let (dg1, outpexec) = GrbInput.addNodesToGraph dg0 prep.currixt [execnode; dsexec] nkAnd (fun _ -> PortStrictB true)
		in
		let (dg2, outptime) = GrbInput.addNodesToGraph dg1 prep.currixt [timenode; dstime] (nkMaximum VTimePoint) (fun _ -> PortMulti VTimePoint)
		in
		let dg3 = RLMap.fold (fun compname oneloc dg' ->
			let vtype = (DG.findnode oneloc.l dg').nkind.outputtype
			in
			let (dg'', _) = GrbInput.addNodesToGraph dg' prep.currixt [outpexec; oneloc] (nkOutput vtype (RLSet.singleton (dataname ^ "." ^ compname))) (fun x -> if x = 0 then PortSingleB true else PortSingle vtype)
			in dg''
		) dsloc dg2
		in
		(dg3, execnode, cexenode, outptime)
and (convertStoppingProcNetwork : stoppingproc array -> sprNetworkNode array -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * ((GrbInput.attrlocationtype * GrbInput.attrlocationtype * GrbInput.attrlocationtype) array)) = fun bnetedges bnetnodes prep currdg execnode cexenode timenode ->
	let result = Array.make ((Array.length bnetedges) + 1) None
	in
	let (dg0, execafter0, cexeafter0, timeafter0) = convertStoppingProcWork bnetedges.(0) {prep with atprocstart = false} currdg execnode cexenode timenode
	in
	result.(0) <- Some (execafter0, cexeafter0, timeafter0);
	let moddg = ref dg0
	in
	let readBNEbyIdx idx =
		if idx >= 0 then bnetedges.(idx) else SPRNil
	and writeResByIdx idx inp =
		if idx >= 0 then (result.(idx) <- inp) else (result.(Array.length bnetedges) <- inp)
	in
	Array.iter (fun bnetnode -> match bnetnode with
		| SPRNBranch (srcidx, btask, trueidx, falseidx) ->
			let Some (exn0, cen0, tmn0) = result.(srcidx)
			in
			let (dg1, Right (exectrue, exectrueDT, execfalse, execfalseDT), timenode') = convertTask btask {prep with atprocstart = false} !moddg exn0 cen0 tmn0
			in
			let (dg2, execaftertrue, cexeaftertrue, timeaftertrue) = convertStoppingProcWork (readBNEbyIdx trueidx) {prep with atprocstart = false} dg1 exectrue exectrueDT timenode'
			in
			let (dg3, execafterfalse, cexeafterfalse, timeafterfalse) = convertStoppingProcWork (readBNEbyIdx falseidx) {prep with atprocstart = false} dg2 execfalse execfalseDT timenode'
			in
			moddg := dg3;
			writeResByIdx trueidx (Some (execaftertrue, cexeaftertrue, timeaftertrue));
			writeResByIdx falseidx (Some (execafterfalse, cexeafterfalse, timeafterfalse))
		| SPRNJoin (srcidxl, tgtidx) ->
			let execnodesl = List.map (fun srcidx -> let Some (exn,_,_) = result.(srcidx) in exn) srcidxl
			and cexenodesl = List.map (fun srcidx -> let Some (_,exn,_) = result.(srcidx) in exn) srcidxl
			and timenodesl = List.map (fun srcidx -> let Some (_,_,tmn) = result.(srcidx) in tmn) srcidxl
			in
			let (dg1, execafter) = GrbInput.addNodesToGraph !moddg prep.currixt execnodesl nkOr (fun _ -> PortUnstrB true)
			in
			let (dg1a, cexeafter) = GrbInput.addNodesToGraph dg1 prep.currixt cexenodesl nkOrDT (fun _ -> PortStrictB false)
			in
			let (dg2, timeafter) = GrbInput.addNodesToGraph dg1a prep.currixt timenodesl (nkMerge VTimePoint) (fun _ -> PortMulti VTimePoint)
			in
			let (dg3, execend, cexeend, timeend) = convertStoppingProcWork (readBNEbyIdx tgtidx) {prep with atprocstart = false} dg2 execafter cexeafter timeafter
			in
			moddg := dg3;
			writeResByIdx tgtidx (Some (execend, cexeend, timeend))
	) bnetnodes;
	(if result.(Array.length bnetedges) = None then result.(Array.length bnetedges) <- result.((Array.length bnetedges) - 1));
	(!moddg, Array.map (fun (Some x) -> x) result)
;;

let rec (convertBPMNwork : anyproc -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t) = fun bproc prep currdg execnode cexenode timenode -> match bproc with
| PRStop stproc -> let (dg,_,_,_) = convertStoppingProcWork stproc prep currdg execnode cexenode timenode in dg
| PRSeq (pr1, pr2) ->
	 let (dg1,exn1,cen1, tim1) = convertStoppingProcWork pr1 prep currdg execnode cexenode timenode
	 in
	 convertBPMNwork pr2 {prep with atprocstart = false} dg1 exn1 cen1 tim1
| PRParal prlist -> List.fold_right (fun prx dg -> convertBPMNwork prx {prep with atprocstart = false} dg execnode cexenode timenode) prlist currdg
| PRBranch (booltask, truebranch, falsebranch) ->
	let (dg0, Right (exectrue, cexetrue, execfalse, cexefalse), timenode') = convertTask booltask {prep with atprocstart = false} currdg execnode cexenode timenode
	in
	let dg1 = convertBPMNwork truebranch {prep with atprocstart = false} dg0 exectrue cexetrue timenode'
	in
	convertBPMNwork falsebranch {prep with atprocstart = false} dg1 execfalse cexefalse timenode'
| PRNetwork (spredges, sprnodes, prends) ->
	let (dg0, allends) = convertStoppingProcNetwork spredges sprnodes prep currdg execnode cexenode timenode
	in
	List.fold_right (fun (stidx, prx) dg -> let (exn,cen,tmn) = allends.(stidx) in convertBPMNwork prx {prep with atprocstart = false} dg exn cen tmn) prends dg0
| PRReplicate (replproc, rprname) ->
	let AITT ixtcont = prep.currixt
	in
	let projmap = IxM [| Some ((), 0, Array.init (Array.length ixtcont.(0)) (fun x -> x)) |]
	in
	let newixt = AITT [| Array.append ixtcont.(0) [| (VInteger, Some rprname) |]  |]
	in
	let (dg1, replexecnode) = GrbInput.putIdNodeOnTop currdg execnode prep.currixt newixt projmap
	in
	let (dg1a, replcexenode) = GrbInput.putIdNodeOnTop dg1 cexenode prep.currixt newixt projmap
	in
	let (dg2, repltimenode) = GrbInput.putIdNodeOnTop dg1a timenode prep.currixt newixt projmap
	in
	let newprep = {
		pcname = rprname :: prep.pcname;
		currixt = newixt;
		atprocstart = true;
		inpdatasets = prep.inpdatasets;
		datasetdecls = prep.datasetdecls;
		datasets = prep.datasets;
		persistents = prep.persistents;
		prptrs = prep.prptrs;
	}
	in
	convertBPMNwork replproc newprep dg2 replexecnode replcexenode repltimenode
;;

let (convertBPMN : anyproc -> datasetdeclaration list -> RLSet.t -> DG.t) = fun bproc datasetdefs inpdatasets ->
	let oc = open_tmpout "procdescr"
	in
	printanyproc oc 0 bproc;
	output_string oc "\n";
	List.iter (fun (dsname, dsdesc) ->
		output_string oc ("Dataset: " ^ dsname ^ " {\n");
		RLMap.iter (fun compname comptype ->
			output_string oc ("  " ^ compname ^ " : " ^ (string_of_valuetype comptype) ^ "\n")
		) dsdesc;
		output_string oc "}\n";
	) datasetdefs;
	RLSet.iter (fun inpdsname ->
		output_string oc ("Input dataset: " ^ inpdsname ^ "\n")
	) inpdatasets;
	close_out oc;
	let dg0 = DG.empty
	and mydatasetdecls = List.fold_right (fun (dsname, dsdesc) m -> RLMap.add dsname (dsname, dsdesc) m) datasetdefs RLMap.empty
	and zeroixt = AITT [| [||] |]
	in
	let persistentDescs = collectPersistentDatasetsProc bproc [] RLMap.empty
	in
	let persistentSet = RLMap.fold (fun dsname _ s -> RLSet.add dsname s) persistentDescs RLSet.empty
	in
	let datasetdims = findBPDatasetDimensions zeroixt bproc
	in
	let (dslocs, dg1) = findBPDataSets bproc mydatasetdecls inpdatasets persistentSet zeroixt datasetdims dg0
	in
	let (dg2, persistentData) = setupPersistentsProc mydatasetdecls persistentDescs dg1
	in
	let procptrColl = collectProcPtrAddresses bproc []
	in
	let (procusedefs, procdefuses) = useDefOfPrPtrs procptrColl
	in
	let (dg3, pointerdata) = findBPPrPtrs procptrColl procusedefs procdefuses dg2
	in
	let prep = {
		pcname = [];
		currixt = zeroixt;
		atprocstart = true;
		inpdatasets = inpdatasets;
		datasetdecls = mydatasetdecls;
		datasets = dslocs;
		persistents = persistentData;
		prptrs = pointerdata;
	}
	in
	let (dg4, execnode) = GrbInput.addNodesToGraph dg3 zeroixt [] nkTrue (fun _ -> PortSingleB true)
	in
	let (dg4a, cexenode) = GrbInput.addNodesToGraph dg4 zeroixt [] nkTrueDT (fun _ -> PortSingleB false)
	in
	let (dg5, timenode) = GrbInput.addNodesToGraph dg4a zeroixt [] nkZeroTimePoint (fun _ -> PortSingle VTimePoint)
	in
	convertBPMNwork bproc prep dg5 execnode cexenode timenode
;;

