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
type normaltaskdefinition = (componentdefinition list) * ((procpointer option * datasetname) list) * (datasetname list);; (* Program, list of inputs, list of outputs *)
type taskdef = NormalTask of taskname * normaltaskdefinition | UpdateTask of taskname * normaltaskdefinition | GuardTask of taskname * definingexpr * ((procpointer option * datasetname) list) | StartEvent of procpointer option * taskname | ProcLauncher of taskname * procpointer * (procname option list);;
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
	| PRBranch (td,tproc,fproc) -> output_string oc tabs, output_string oc "PRBranch(\n"; printtask oc (tabnum + 1) td; printanyproc oc (tabnum + 1) tproc; printanyproc oc (tabnum + 1) fproc; output_string oc tabs; output_string oc ")\n"
	| PRReplicate (aproc, prname) -> output_string oc tabs; output_string oc "PRReplicate( "; output_string oc prname; output_string oc "\n"; printanyproc oc (tabnum + 1) aproc; output_string oc tabs; output_string oc ")\n"
	| PRNetwork (sproca, spnna, tails) -> output_string oc tabs; output_string oc "PRNetwork{\n"; output_string oc tabs; output_string oc "EDGES:\n"; Array.iter (fun sproc -> printstoppingproc oc (tabnum + 1) sproc) sproca; output_string oc tabs; output_string oc "NODES:\n"; Array.iter (fun nnn -> printnetworknode oc (tabnum + 1) nnn) spnna; output_string oc tabs; output_string oc "TAILS:\n"; List.iter (fun (idx,aproc) -> output_string oc tabs; output_string oc (string_of_int idx); output_string oc ":\n"; printanyproc oc (tabnum + 1) aproc) tails; output_string oc tabs; output_string oc "}\n"
and printstoppingproc oc tabnum = 
	let tabs = String.make (2 * tabnum) ' '
	in function
	| SPRNil -> output_string oc tabs; output_string oc "SPRNIL()\n"
	| SPRTask td -> output_string oc tabs; output_string oc "SPRTask(\n"; printtask oc (tabnum + 1) td; output_string oc tabs; output_string oc ")\n"
	| SPRParal sprocl -> output_string oc tabs; output_string oc "SPRPARAL[\n"; List.iter (fun p -> printstoppingproc oc (tabnum + 1) p) sprocl; output_string oc tabs; output_string oc "]\n"
	| SPRBranch (td,tproc,fproc) -> output_string oc tabs, output_string oc "SPRBranch(\n"; printtask oc (tabnum + 1) td; printstoppingproc oc (tabnum + 1) tproc; printstoppingproc oc (tabnum + 1) fproc; output_string oc tabs; output_string oc ")\n"
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
and printinplist oc inplist = output_string oc "["; output_string oc (String.concat "; " (List.map (fun (prptropt, dsname) -> dsname ^ "@" ^ (match prptropt with None -> "Here" | Some c -> NewName.to_string c)) inplist)); output_string oc "]"
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
	List.iter (fun (prptropt,dsname) -> output_string oc tabs; output_string oc (dsname ^ "@" ^ (match prptropt with None -> "Here" | Some c -> NewName.to_string c) ^ "\n" )) inpl;
	output_string oc tabs; output_string oc "OUTPUTS: "; output_string oc (String.concat ", " outpl); output_string oc "\n"
;;

type prptrdesctype = {
(*	tgt : procname option list; *)
	checknodeid : GrbInput.attrlocationtype; (* ID of the AND-node *)
	procpath : procname list; (* the innermost starts the list *)
	numdatadims : int;
	numjointdims : int; (* how many dimensions the initiator and target have in common *)
	backptr : procpointer;
};;

type datasetlocationtype = GrbInput.attrlocationtype * GrbInput.attrlocationtype * (GrbInput.attrlocationtype RLMap.t) * indextypetype;; (* exist node, time node, attribute nodes, indextype of everything *)

type persistencykindtype = PersSet | PersVar | PersWriteOnce;; (* determined from the name of the dataset *)

type persistentwritetype = {
	timepointnode : GrbInput.attrlocationtype;
	updatenode : GrbInput.attrlocationtype RLMap.t; (* indexed with names of the components of the data set *)
};;

type persistentdesctype = {
	datanode : GrbInput.attrlocationtype RLMap.t; (* indexed with names of components of the data set *)
	dataixt : indextypetype;
	updatemode : persistencykindtype;
	writings : persistentwritetype RLMap.t; (* indexed with names of update tasks *)
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

let rec (findSBPDataSets : stoppingproc -> datasetdeclaration RLMap.t -> RLSet.t -> RLSet.t -> indextypetype -> DG.t -> (datasetlocationtype * bool) RLMap.t * DG.t) = fun sproc dsdescs inpdatasets persistents currixt dg0 ->
let handleTaskDataFlow m dg' dsname execkind timekind mainkind =
	let (AITT aa) = currixt
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
		inputindextype = currixt;
		outputindextype = currixt;
		ixtypemap = ixmap;
	}
	and timenode = {
		nkind = timekind;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = currixt;
		outputindextype = currixt;
		ixtypemap = ixmap;
	}
	in
	currdg := DG.addnode execnode (DG.addnode timenode !currdg);
	let locnodes = RLMap.fold (fun compname compval mm ->
		let locnode = {
			nkind = mainkind compval (dsname ^ "." ^ compname);
			id = NewName.get ();
			inputs = PortMap.empty;
			inputindextype = currixt;
			outputindextype = currixt;
			ixtypemap = ixmap;
		}
		in
		currdg := DG.addnode locnode !currdg;
		RLMap.add compname {l = locnode.id; t = RLSet.singleton dsname} mm
	) thisdsdecl RLMap.empty
	in
	(RLMap.add dsname (({l = execnode.id; t = RLSet.singleton dsname}, {l = timenode.id; t = RLSet.singleton dsname}, locnodes, currixt), false) m, !currdg)
in
let handleTaskOutput dg0 btask = match btask with
	| NormalTask (_, (_, _, dsnl))
	| UpdateTask (_, (_, _, dsnl)) ->
		List.fold_right (fun dsname (m, dg') ->
			if RLSet.mem dsname persistents then
			begin
				(RLMap.add dsname (({l = NewName.invalid_id; t = RLSet.empty;}, {l = NewName.invalid_id; t = RLSet.empty;}, RLMap.empty, AITT [||] ), true) m, dg')
			end
			else
			begin
				handleTaskDataFlow m dg' dsname nkOr (nkMerge VInteger) (fun x y -> nkMerge x)
			end
		) dsnl (RLMap.empty, dg0)
	| _ -> (RLMap.empty, dg0)
and handleTaskInput dg0 btask = match btask with
	| NormalTask (_, (_, inpds, _))
	| UpdateTask (_, (_, inpds, _))
	| GuardTask (_, _, inpds) ->
		List.fold_right (fun (_, dsname) (m, dg') ->
			if (RLSet.mem dsname inpdatasets) && (not (RLSet.mem dsname persistents)) then
			begin
				handleTaskDataFlow m dg' dsname (nkInputExists dsname) (nkOperation 0 VInteger (OPIntConst 0)) (fun x y -> nkInput x y false)
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
		let (m', dg'') = findSBPDataSets spr dsdescs inpdatasets persistents currixt dg'
		in (RLMap.union m m', dg'')
	) sprlist (RLMap.empty, dg0)
| SPRBranch (btask, tproc, fproc) ->
	let (m1, dg1) = handleTaskInput dg0 btask
	in
	let (m2, dg2) = findSBPDataSets tproc dsdescs inpdatasets persistents currixt dg1
	in
	let (m3, dg3) = findSBPDataSets fproc dsdescs inpdatasets persistents currixt dg2
	in
	(RLMap.union m1 (RLMap.union m2 m3), dg3)
| SPRNetwork (spredges, sprnodes) ->
	let (m1, dg1) = Array.fold_right (fun spr (m, dg') ->
		let (m', dg'') = findSBPDataSets spr dsdescs inpdatasets persistents currixt dg'
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
	let (m1, dg1) = findSBPDataSets spr1 dsdescs inpdatasets persistents currixt dg0
	in
	let (m2, dg2) = findSBPDataSets spr2 dsdescs inpdatasets persistents currixt dg1
	in
	(RLMap.union m1 m2, dg2)
| SPRPublish _ -> (RLMap.empty, dg0)
;;

let rec (findBPDataSets : anyproc -> datasetdeclaration RLMap.t -> RLSet.t -> RLSet.t -> indextypetype -> DG.t -> (datasetlocationtype * bool) RLMap.t * DG.t) = fun bproc dsdescs inpdatasets persistents currixt dg0 -> match bproc with
| PRStop sbproc -> findSBPDataSets sbproc dsdescs inpdatasets persistents currixt dg0
| PRSeq (spr1, pr2) ->
	let (m1, dg1) = findSBPDataSets spr1 dsdescs inpdatasets persistents currixt dg0
	in
	let (m2, dg2) = findBPDataSets pr2 dsdescs inpdatasets persistents currixt dg1
	in
	(RLMap.union m1 m2, dg2)
| PRParal bprocl ->
	List.fold_right (fun pr (m, dg') ->
		let (m', dg'') = findBPDataSets pr dsdescs inpdatasets persistents currixt dg'
		in (RLMap.union m m', dg'')
	) bprocl (RLMap.empty, dg0)
| PRBranch (btask, tproc, fproc) ->
	let (m1, dg1) = findSBPDataSets (SPRTask btask) dsdescs inpdatasets persistents currixt dg0
	in
	let (m2, dg2) = findBPDataSets tproc dsdescs inpdatasets persistents currixt dg1
	in
	let (m3, dg3) = findBPDataSets fproc dsdescs inpdatasets persistents currixt dg2
	in
	(RLMap.union m1 (RLMap.union m2 m3), dg3)
| PRNetwork (spredges, sprnodes, prends) ->
	let (m1, dg1) = findSBPDataSets (SPRNetwork (spredges, sprnodes)) dsdescs inpdatasets persistents currixt dg0
	in
	let (m2, dg2) = List.fold_right (fun (_,pr) (m, dg') ->
		let (m', dg'') = findBPDataSets pr dsdescs inpdatasets persistents currixt dg'
		in (RLMap.union m m', dg'')
	) prends (m1, dg1)
	in
	(RLMap.union m1 m2, dg2)
| PRReplicate (rproc, rprname) ->
	let (AITT aa) = currixt
	in
	let newixt = AITT [| Array.append aa.(0) [| (VInteger, Some rprname) |] |]
	in
	findBPDataSets rproc dsdescs inpdatasets persistents newixt dg0
;;

let rec combinetwopaths currpath procpath = match currpath, procpath with
| xs, [] -> (xs, 0)
| (x::xs), (None::ys) -> combinetwopaths xs ys
| xs, ((Some y) :: ys) -> let (res,c) = combinetwopaths (y::xs) ys in (res, c+1)
;;

let perslocunion dsname fv1 fv2 = match fv1,fv2 with
| None, x -> x
| x, None -> x
| Some (path1, upds1), Some (path2, upds2) -> Some (path1, List.append upds1 upds2)
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
	let currdg = ref dg0
	in
	let rightside = RLMap.mapi (fun dsname (defpath, updlist) ->
		let dixtcomp0 = Array.of_list (List.map (fun s -> (VInteger, Some s)) (List.rev defpath))
		and (_, compdecls) = RLMap.find dsname dssdesc
		in
		let dixtmap = IxM [| Some ((), 0, Array.init (Array.length dixtcomp0) (fun x -> x)) |]
		in
		let inpnodes = RLMap.mapi (fun compname comptype ->
			let inpnode = {
				nkind = nkInput comptype (dsname ^ "." ^ compname) false;
				id = NewName.get ();
				inputs = PortMap.empty;
				inputindextype = AITT [| dixtcomp0 |];
				outputindextype = AITT [| dixtcomp0 |];
				ixtypemap = dixtmap;
			}
			in
			currdg := DG.addnode inpnode !currdg;
			{l = inpnode.id; t = RLSet.empty}
		) compdecls
		in
		let dupdmode = 
			if ((String.length dsname) >= 5) && ((String.uppercase (String.sub dsname 0 5)) = "STATE") then PersVar else
			if  ((String.length dsname) >= 6) && ((String.uppercase (String.sub dsname 0 6)) = "RECORD") then PersWriteOnce else PersSet
		in
		let writingdata = List.fold_right (fun (updtname, updtpath) m ->
			let uixtcomp0 = Array.of_list (List.map (fun s -> (VInteger, Some s)) (List.rev updtpath))
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
			let (dg1, tploc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) (Array.to_list takedimlocs) (nkTimePoint updtname (Array.length takedimlocs)) (fun x -> PortOperInput (x+1))
			in
			currdg := dg1;
			let updlocs = RLMap.mapi (fun compname comptype ->
				let (dg2, updloc) = GrbInput.addNodesToGraph !currdg (AITT [| uixtcomp0 |]) [tploc] (nkTuple [("idx", VInteger);("data", comptype)]) (fun _ -> PortOperInput 1)
				in
				currdg := dg2;
				updloc
			) compdecls
			in
			RLMap.add updtname {timepointnode = tploc; updatenode = updlocs;} m
		) updlist RLMap.empty
		in
		{
			datanode = inpnodes;
			dataixt = AITT [| dixtcomp0 |];
			updatemode = dupdmode;
			writings = writingdata;
		}
	) persdesc
	in
	(!currdg, rightside)
;;

let (collectTaskPtrAddresses : taskdef -> procname list -> (procname list * (procname list * int) option) IdtMap.t) = fun btask currpath ->
match btask with
| StartEvent (Some prptr, _) -> IdtMap.singleton prptr (currpath, None)
| StartEvent (None, _) -> IdtMap.empty
| ProcLauncher (_, nprptr, procpath) -> let (res,c) = combinetwopaths currpath procpath in (print_string ("Process pointer " ^ (NewName.to_string nprptr) ^ " at path " ^ (String.concat ":" currpath) ^ " points to the path " ^ (String.concat ":" res) ^ " with indep. number " ^ (string_of_int c)); print_newline (); IdtMap.singleton nprptr (currpath, Some (res, c)))
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
| PRReplicate (rproc, rprname) -> collectProcPtrAddresses rproc (rprname :: currpath)
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
					in
					currdg := DG.addnode compnode !currdg;
					currdg := DG.addedge ((identityIndexMap addrgennodes.(c).id addrgennodes.(c).outputindextype, NewName.get()), compnode.id, PortCompare) !currdg;
					currdg := DG.addedge ((IxM [| Some (dtakedimnodes.(c + trunklen).id, 0, dToBProjbackmap) |], NewName.get ()), compnode.id, PortCompare) !currdg;
					compnode
				)
				in
				let complocations = Array.to_list (Array.map (fun n -> {l = n.id; t = RLSet.empty}) comparisonnodes)
				in
				let (dgn, andloc) = GrbInput.addNodesToGraph !currdg (AITT [| bixtcomp0 |]) complocations nkAnd (fun _ -> PortStrictB)
				in
				(dgn, ({checknodeid = andloc; procpath = spath; numdatadims = sindepnum + trunklen; numjointdims = trunklen; backptr = sptr;} :: foundptrll))
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
				in
				currdg := DG.addnode compnode !currdg;
				currdg := DG.addedge ((IxM [| Some (addrgennodes.(c).id, 0, dToBProjbackmap) |], NewName.get()), compnode.id, PortCompare) !currdg;
				currdg := DG.addedge ((IxM [| Some (stakedimnodes.(c + trunklen).id, 0, sToBProjbackmap) |], NewName.get ()), compnode.id, PortCompare) !currdg;
				compnode
			)
			in
			let complocations = Array.to_list (Array.map (fun n -> {l = n.id; t = RLSet.empty}) comparisonnodes)
			in
			let (dgn, andloc) = GrbInput.addNodesToGraph !currdg (AITT [| bixtcomp0 |]) complocations nkAnd (fun _ -> PortStrictB)
			in
			print_string ("The back pointer is ptr no. " ^ (NewName.to_string (IdtMap.find dptr defuses)) ^ "\n");
			(dgn, IdtMap.add dptr [{checknodeid = andloc; procpath = spath; numdatadims = dindepnum + trunklen; numjointdims = trunklen; backptr = IdtMap.find dptr defuses;}] foundptrs)
		end
	) ptrcollection (dg0, IdtMap.empty)
;;

let (collectRemoteDataset : procpointer -> datasetname -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * datasetlocationtype) = fun prptr dsname prep dg0 execnode timenode ->
	let ((dsexec, dstime, dscomplocs, (AITT dsixtype)), isPersistent) = RLMap.find dsname prep.datasets
	and actualptrdescs = IdtMap.find prptr prep.prptrs
	in
	if isPersistent then
	begin
		raise (Failure "Persistent datasets are not accessed through process pointers")
	end
	else
	begin
		let currdg = ref dg0
		in
		let (llexecs, lltimes, llcomps) = List.fold_right (fun oneptrdesc (llexec', lltime', llcomp') ->
			let andnode = DG.findnode oneptrdesc.checknodeid.l !currdg
			in
			let (AITT anb) = andnode.outputindextype
			in
			let projmap = IxM [| Some ((), 0, Array.init oneptrdesc.numdatadims (fun x -> x)) |]
			in
			let dsexecnode = DG.findnode dsexec.l !currdg
			in
			let (AITT dseb) = dsexecnode.outputindextype
			in
			if not (Array.fold_left (&&) true (Array.mapi (fun idx ixtmem -> ixtmem = anb.(0).(idx)) dseb.(0))) then ((None :: llexec'), (None :: lltime'), (None :: llcomp')) else
			let applyToOneNode nowdg oneloc pnkFilter filterInps pnkLongMerge mergePort =
				let (nextdg1, onelochere) = GrbInput.putIdNodeOnTop nowdg oneloc (AITT dsixtype) (AITT anb) projmap
				in
				let vtype = (DG.findnode onelochere.l nextdg1).nkind.outputtype
				in
				let (nextdg2, filterloc) = GrbInput.addNodesToGraph nextdg1 (AITT anb) [oneptrdesc.checknodeid; onelochere] (pnkFilter vtype) (filterInps vtype)
				in
				let numMergedDims = (Array.length anb.(0)) - oneptrdesc.numdatadims + oneptrdesc.numjointdims
				in
				let mergeoit = AITT [| Array.init numMergedDims (fun x -> if x < oneptrdesc.numjointdims then anb.(0).(x) else anb.(0).(x + oneptrdesc.numdatadims - oneptrdesc.numjointdims)) |]
				and mergeitm = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> if x < oneptrdesc.numjointdims then x else x + oneptrdesc.numdatadims - oneptrdesc.numjointdims)) |]
				in
				let mergenode = {
					nkind = pnkLongMerge vtype;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = (AITT anb);
					outputindextype = mergeoit;
					ixtypemap = mergeitm;
				}
				in
				let nextdg3 = DG.addedge ((IxM [| Some (filterloc.l, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenode.id, mergePort vtype) (DG.addnode mergenode nextdg2)
				in
				let finalprojmap = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> x)) |]
				in
				GrbInput.putIdNodeOnTop nextdg3 {l = mergenode.id; t = filterloc.t} mergeoit prep.currixt finalprojmap
			in
			let (dg1, dscomplocshere) = RLMap.fold (fun compname oneloc (nowdg, m) ->
				let (nextdg3, mergeloc) = applyToOneNode nowdg oneloc nkFilter (fun vtype x -> if x = 0 then PortSingleB else PortSingle vtype) nkLongMerge (fun vtype -> PortSingle vtype)
				in
				(nextdg3, RLMap.add compname mergeloc m)
			) dscomplocs (!currdg, RLMap.empty)
			in
			let (dg2, dsexechere) = applyToOneNode dg1 dsexec (fun _ -> nkAnd) (fun _ _ -> PortStrictB) (fun _ -> nkLongOr) (fun _ -> PortSingleB)
			in
			let (dg3, dstimehere) = applyToOneNode dg2 dstime nkFilter (fun vtype x -> if x = 0 then PortSingleB else PortSingle vtype) nkLongMerge (fun vtype -> PortSingle vtype)
			in
			(currdg := dg3; ((Some dsexechere :: llexec'), (Some dstimehere :: lltime'), (Some dscomplocshere :: llcomp')))
		) actualptrdescs ([], [], [])
		in
		let mkMergeAndIdNodes inplist isMerge tgtVtype =
			let (dg1, newloc) = addNodesToGraph !currdg prep.currixt inplist (if isMerge then nkMerge tgtVtype else nkOr) (if isMerge then (fun _ -> PortMulti tgtVtype) else (fun _ -> PortUnstrB))
			in
			currdg := dg1; newloc
		in
		let rec cleanList = function
			| [] -> []
			| None :: xs -> cleanList xs
			| (Some x) :: xs -> x :: (cleanList xs)
		in
		let resExec = mkMergeAndIdNodes (cleanList llexecs) false VBoolean
		and resTime = mkMergeAndIdNodes (cleanList lltimes) true VInteger
		and resComps =
			let clcomps = cleanList llcomps
			and (_, comptypes) = RLMap.find dsname prep.datasetdecls
			in
			RLMap.fold (fun compname oneloc m ->
				RLMap.add compname (mkMergeAndIdNodes (List.map (RLMap.find compname) clcomps) true (RLMap.find compname comptypes)) m
			) dscomplocs RLMap.empty
		in
		let (dgf1, resExec') = addNodesToGraph !currdg prep.currixt [resExec; execnode] nkAnd (fun _ -> PortStrictB)
		in
		let (dgf2, resTime') = addNodesToGraph dgf1 prep.currixt [resTime; timenode] (nkMaximum VInteger) (fun _ -> PortMulti VInteger)
		in
		(dgf2, (resExec', resTime', resComps, prep.currixt))
	end
;;

let (collectDataset : procpointer option -> datasetname -> taskname -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * datasetlocationtype) = fun maybeprptr dsname tname prep dg0 execnode timenode -> match maybeprptr with
| Some prptr -> collectRemoteDataset prptr dsname prep dg0 execnode timenode
| None ->
	let ((dsexec, dstime, dscomplocs, (AITT dsixtype)), isPersistent) = RLMap.find dsname prep.datasets
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
		let (dg1, tploc) = GrbInput.addNodesToGraph !currdg prep.currixt (timenode :: (Array.to_list takedims)) (nkTimePoint tname (Array.length takedims)) (fun x -> if x = 0 then PortSingle VInteger else PortOperInput x)
		and combinestring = if persdata.updatemode = PersSet then "union" else if persdata.updatemode = PersVar then "overwrite" else "takefirstnon0"
		in
		currdg := dg1;
		let dscomplocs' = RLMap.mapi (fun compname comptype ->
			let (dg2, liftorigloc) = GrbInput.putIdNodeOnTop !currdg (RLMap.find compname persdata.datanode) persdata.dataixt prep.currixt (IxM [| Some ((), 0, Array.init (Array.length dixt.(0)) (fun x -> x)) |])
			in
			let updinnertype = (DG.findnode liftorigloc.l dg2).nkind.outputtype
			in
			let updvtype = VTuple [("idx", VInteger); ("data", updinnertype)]
			in
			currdg := dg2;
			let longupdlocs = RLMap.fold (fun writetname writeinfo ll ->
				let (AITT wixt) = (DG.findnode writeinfo.timepointnode.l !currdg).outputindextype
				in
				let combixt0 = Array.init ((Array.length cixt.(0)) + (Array.length wixt.(0)) - (Array.length dixt.(0))) (fun x -> if x < (Array.length cixt.(0)) then cixt.(0).(x) else wixt.(0).(x - (Array.length cixt.(0)) + (Array.length dixt.(0))))
				in
				let cbackmap = Array.init (Array.length cixt.(0)) (fun x -> x)
				and wbackmap = Array.init (Array.length wixt.(0)) (fun x -> if x < (Array.length dixt.(0)) then x else x + (Array.length cixt.(0)) - (Array.length dixt.(0)) )
				in
				let combinedixt = AITT [| combixt0 |]
				and cprojmap = IxM [| Some ((), 0, cbackmap) |]
				and wprojmap = IxM [| Some ((), 0, wbackmap) |]
				in
				let (ndg1, widetploc) = GrbInput.putIdNodeOnTop !currdg tploc prep.currixt combinedixt cprojmap
				in
				let (ndg2, widewritetime) = GrbInput.putIdNodeOnTop ndg1 writeinfo.timepointnode (AITT wixt) combinedixt wprojmap
				in
				let (ndg3, compareloc) = GrbInput.addNodesToGraph ndg2 combinedixt [widewritetime; widetploc] (nkOperation 2 VBoolean OPLessThan) (fun x -> PortOperInput (x+1))
				in
				let updateloc = RLMap.find compname writeinfo.updatenode
				in
				let (ndg4, wideupdateloc) = GrbInput.putIdNodeOnTop ndg3 updateloc (AITT wixt) combinedixt wprojmap
				in
				let (ndg5, filterloc) = GrbInput.addNodesToGraph ndg4 combinedixt [compareloc; wideupdateloc] (nkFilter updvtype) (fun x -> if x = 0 then PortSingleB else PortSingle updvtype)
				in
				let longcombinenode = {
					nkind = nkLongUpdCombine combinestring updinnertype;
					id = NewName.get ();
					inputs = PortMap.empty;
					inputindextype = combinedixt;
					outputindextype = prep.currixt;
					ixtypemap = cprojmap;
				}
				in
				let ndg6 = DG.addedge ((identityIndexMap filterloc.l combinedixt, NewName.get ()), longcombinenode.id, PortSingle updvtype) (DG.addnode longcombinenode ndg5)
				in
				currdg := ndg6;
				{l = longcombinenode.id; t = filterloc.t} :: ll
			) persdata.writings []
			in
			let (dg3, newcomploc) = GrbInput.addNodesToGraph !currdg prep.currixt ( (* liftorigloc :: *) longupdlocs) (nkUpdCombine combinestring updinnertype) (fun x -> if x = 0 then PortSingle updinnertype else PortMulti updvtype)
			in
			currdg := dg3;
			newcomploc
		) dscompdecls
		in
		(!currdg, (execnode, tploc, dscomplocs', prep.currixt))
	end
	else
	begin
		let projmap = IxM [| Some ((), 0, Array.init (Array.length dsixtype.(0)) (fun x -> x) ) |]
		in
		let (dg1, dsexec') = GrbInput.putIdNodeOnTop dg0 dsexec (AITT dsixtype) prep.currixt projmap
		in
		let (dg2, dstime') = GrbInput.putIdNodeOnTop dg1 dstime (AITT dsixtype) prep.currixt projmap
		in
		let (dg3, dscomplocs') = RLMap.fold (fun compname oneloc (dg', m) ->
			let (dg'', oneloc') = GrbInput.putIdNodeOnTop dg' oneloc (AITT dsixtype) prep.currixt projmap
			in
			(dg'', RLMap.add compname oneloc' m)
		) dscomplocs (dg2, RLMap.empty)
		in
		let (dg4, dsexec'') = GrbInput.addNodesToGraph dg3 prep.currixt [dsexec'; execnode] nkAnd (fun _ -> PortStrictB)
		in
		let (dg5, dstime'') = GrbInput.addNodesToGraph dg4 prep.currixt [dstime'; timenode] (nkMaximum VInteger) (fun _ -> PortMulti VInteger)
		in
		(dg5, (dsexec'', dstime'', dscomplocs', prep.currixt))
	end
;;

let (writeDataSet : taskname -> datasetname -> graphpreparationtype -> DG.t -> datasetlocationtype -> DG.t * (GrbInput.attrlocationtype option)) = fun tname dsname prep dg0 (dsexecwr, dstimewr, dscolswr, _) ->
	let ((dsexec, dstime, dscomplocs, (AITT dsixtype)), isPersistent) = RLMap.find dsname prep.datasets
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
		let dg1 = DG.addedge ((IxM [| Some (dstimewr.l, 0, backmap) |], NewName.get ()), perspointdata.timepointnode.l, PortSingle VInteger) dg0
		in
		let dg2 = RLMap.fold (fun compname onelocwr dg' ->
			let oneloc = RLMap.find compname perspointdata.updatenode
			in
			let vtype = (DG.findnode oneloc.l dg').nkind.outputtype
			in
			DG.addedge ((IxM [| Some (onelocwr.l, 0, backmap) |], NewName.get ()), oneloc.l, PortOperInput 2) dg'
		) dscolswr dg1
		in
		(dg2, Some perspointdata.timepointnode)
	end
	else
	begin
		let dg1 = DG.addedge ((IxM [| Some (dsexecwr.l, 0, backmap) |], NewName.get ()), dsexec.l, PortUnstrB) dg0
		in
		let dg2 = DG.addedge ((IxM [| Some (dstimewr.l, 0, backmap) |], NewName.get ()), dstime.l, PortMulti VInteger) dg1
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
	let (_,_,dslocs,_) = RLMap.find dsname inpdatasets
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
			let nextdg3 = DG.addedge ((IxM [| Some (andnode.id, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenode.id, PortSingleB) (DG.addnode mergenode dg')
			in
			let finalprojmap = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> x)) |]
			in
			let (dg'', projloc) = GrbInput.putIdNodeOnTop nextdg3 {l = mergenode.id; t = RLSet.empty} mergeoit prep.currixt finalprojmap
			in (dg'', projloc :: ll)
		end else (dg', ll)
	) ptrdesc (dg0, [])
	in
	GrbInput.addNodesToGraph dg1 prep.currixt locchecks nkOr (fun _ -> PortUnstrB)
;;

let (convertTask : taskdef -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * ((GrbInput.attrlocationtype, GrbInput.attrlocationtype * GrbInput.attrlocationtype) either) * GrbInput.attrlocationtype) = fun btask prep dg0 execnode timenode -> match btask with
| NormalTask (tname, (_, proginps, _))
| UpdateTask (tname, (_, proginps, _))
| GuardTask (tname, _, proginps) ->
	let (prog, isGuard, progouts) = (match btask with NormalTask (_, (p,_,po)) | UpdateTask (_, (p,_,po)) -> (p, false, po) | GuardTask (_,s,_) -> ([(("",""),s)], true, []) )
	and isUpdate = (match btask with UpdateTask _ -> true | _ -> false)
	in
	let (dg1, inpdatasets) = List.fold_right (fun (pptropt, dsname) (dg', m) ->
		let (dg'', dsloc) = collectDataset pptropt dsname tname prep dg' execnode timenode
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
	let (execnodelist, timenodelist) = RLMap.fold (fun _ (dsexec, dstime, _, _) (l1,l2) ->
		((dsexec :: l1), (dstime :: l2))
	) inpdatasets ([execnode], [timenode])
	in
	let (dg3, allexec) = GrbInput.addNodesToGraph dg2 prep.currixt execnodelist nkAnd (fun _ -> PortStrictB)
	in
	let (dg4, alltime) = GrbInput.addNodesToGraph dg3 prep.currixt timenodelist (nkMaximum VInteger) (fun _ -> PortMulti VInteger)
	in
	if isGuard then
	begin
		let guardloc = RLMap.find "" (RLMap.find "" outps)
		in
		let (dg5, posguard) = GrbInput.addNodesToGraph dg4 prep.currixt [allexec; guardloc] nkAnd (fun _ -> PortStrictB)
		in
		let (dg6, notguardloc) = GrbInput.addNodesToGraph dg5 prep.currixt [guardloc] nkNot (fun _ -> PortSingleB)
		in
		let (dg7, negguard) = GrbInput.addNodesToGraph dg6 prep.currixt [allexec; notguardloc] nkAnd (fun _ -> PortStrictB)
		in
		(dg7, Right (posguard, negguard), alltime)
	end
	else
	begin
		let (dg5, newtimes) = RLMap.fold (fun newdsname newdslocs (dg', timell) ->
			let (dg'', posstimeloc) = writeDataSet tname newdsname prep dg' (allexec, alltime, newdslocs, prep.currixt)
			in
			match posstimeloc with
			| None -> (dg'', timell)
			| Some realtimeloc -> (dg'', realtimeloc :: timell)
		) outps (dg4, [])
		in
		let (dg6, alltime') = if newtimes = [] then (dg5, alltime) else GrbInput.addNodesToGraph dg5 prep.currixt (alltime :: newtimes) (nkMaximum VInteger) (fun x -> PortMulti VInteger)
		in
		(dg6, Left allexec, alltime')
	end
| StartEvent (Some prptr, tname) ->
	let prptrdescl = IdtMap.find prptr prep.prptrs
	in
	let (dg1, locchecks) = List.fold_right (fun ptrpoint (dg', ll) ->
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
		let nextdg3 = DG.addedge ((IxM [| Some (andnode.id, 0, Array.init (Array.length anb.(0)) (fun x -> x)) |], NewName.get ()), mergenode.id, PortSingleB) (DG.addnode mergenode dg')
		in
		let finalprojmap = IxM [| Some ((), 0, Array.init numMergedDims (fun x -> x)) |]
		in
		let (dg'', projloc) = GrbInput.putIdNodeOnTop nextdg3 {l = mergenode.id; t = RLSet.empty} mergeoit prep.currixt finalprojmap
		in (dg'', projloc :: ll)
	) prptrdescl (dg0, [])
	in
	let (dg2, ornodeloc) = GrbInput.addNodesToGraph dg1 prep.currixt locchecks nkOr (fun _ -> PortUnstrB)
	in
	let (dg3, startnodeloc) = GrbInput.addNodesToGraph dg2 prep.currixt [ornodeloc; execnode] nkAnd (fun _ -> PortStrictB)
	in
	(dg3, Left startnodeloc, timenode)
| StartEvent (None, tname) ->
	let (dg1, invokenodeloc) = GrbInput.addNodesToGraph dg0 prep.currixt [] (nkInputExists tname) (fun _ -> PortSingleB)
	in
	let (dg2, startnodeloc) = GrbInput.addNodesToGraph dg1 prep.currixt [execnode; invokenodeloc] nkAnd (fun _ -> PortStrictB)
	in
	(dg2, Left startnodeloc, timenode)
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
	in
	let dg1 = DG.addedge ((projmap, NewName.get ()), backptrdesc.checknodeid.l, PortStrictB) dg0
	in
	(dg1, Left execnode, timenode)
;;

let rec (convertStoppingProcWork : stoppingproc -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * GrbInput.attrlocationtype * GrbInput.attrlocationtype) = fun bproc prep currdg execnode timenode -> match bproc with
| SPRNil -> (currdg, execnode, timenode)
| SPRTask taskdesc ->
	let (dg0, Left execnode', timenode') = convertTask taskdesc prep currdg execnode timenode
	in
	(dg0, execnode', timenode')
| SPRParal sprlist -> if sprlist = [] then (currdg, execnode, timenode) else
	let (dg0, exnlist, timlist) = List.fold_right (fun prx (dg, exl, tml) ->
		let (dg', exn', tmn') = convertStoppingProcWork prx {prep with atprocstart = false} dg execnode timenode
		in (dg', (exn' :: exl), (tmn' :: tml))
	) sprlist (currdg, [], [])
	in
	let (dg1, nexecnode) = GrbInput.addNodesToGraph dg0 prep.currixt exnlist nkAnd (fun _ -> PortStrictB)
	in
	let (dg2, ntimenode) = GrbInput.addNodesToGraph dg1 prep.currixt timlist (nkMaximum VInteger) (fun _ -> PortMulti VInteger)
	in
	(dg2, nexecnode, ntimenode)
| SPRBranch (booltask, truebranch, falsebranch) ->
	let (dg0, Right (exectrue, execfalse), timenode') = convertTask booltask {prep with atprocstart = false} currdg execnode timenode
	in
	let (dg1, execaftertrue, timeaftertrue) = convertStoppingProcWork truebranch {prep with atprocstart = false} dg0 exectrue timenode'
	in
	let (dg2, execafterfalse, timeafterfalse) = convertStoppingProcWork falsebranch {prep with atprocstart = false} dg1 execfalse timenode'
	in
	let (dg3, execafter) = GrbInput.addNodesToGraph dg2 prep.currixt [execaftertrue; execafterfalse] nkOr (fun _ -> PortUnstrB)
	in
	let (dg4, timeafter) = GrbInput.addNodesToGraph dg3 prep.currixt [timeaftertrue; timeafterfalse] (nkMerge VInteger) (fun _ -> PortMulti VInteger)
	in
	(dg4, execafter, timeafter)
| SPRNetwork (spredges, sprnodes) ->
	let lastidx = (Array.length spredges) - 1
	in
	let (dgres, allends) = convertStoppingProcNetwork spredges sprnodes prep currdg execnode timenode
	in
	let (execlast, timelast) = allends.(lastidx)
	in
	(dgres, execlast, timelast)
| SPRSeq (pr1, pr2) ->
	 let (dg1,exn1, tim1) = convertStoppingProcWork pr1 prep currdg execnode timenode
	 in
	 convertStoppingProcWork pr2 {prep with atprocstart = false} dg1 exn1 tim1
| SPRPublish (prptropt, dataname) ->
		let (dg0, (dsexec, dstime, dsloc, _)) = collectDataset prptropt dataname ("Publish " ^ dataname) prep currdg execnode timenode
		in
		let (dg1, outpexec) = GrbInput.addNodesToGraph dg0 prep.currixt [execnode; dsexec] nkAnd (fun _ -> PortStrictB)
		in
		let (dg2, outptime) = GrbInput.addNodesToGraph dg1 prep.currixt [timenode; dstime] (nkMaximum VInteger) (fun _ -> PortMulti VInteger)
		in
		let dg3 = RLMap.fold (fun compname oneloc dg' ->
			let vtype = (DG.findnode oneloc.l dg').nkind.outputtype
			in
			let (dg'', _) = GrbInput.addNodesToGraph dg' prep.currixt [outpexec; oneloc] (nkOutput vtype (RLSet.singleton (dataname ^ "." ^ compname))) (fun x -> if x = 0 then PortSingleB else PortSingle vtype)
			in dg''
		) dsloc dg2
		in
		(dg3, execnode, outptime)
and (convertStoppingProcNetwork : stoppingproc array -> sprNetworkNode array -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t * ((GrbInput.attrlocationtype * GrbInput.attrlocationtype) array)) = fun bnetedges bnetnodes prep currdg execnode timenode ->
	let result = Array.make (Array.length bnetedges) None
	in
	let (dg0, execafter0, timeafter0) = convertStoppingProcWork bnetedges.(0) {prep with atprocstart = false} currdg execnode timenode
	in
	result.(0) <- Some (execafter0, timeafter0);
	let moddg = ref dg0
	in
	Array.iter (fun bnetnode -> match bnetnode with
		| SPRNBranch (srcidx, btask, trueidx, falseidx) ->
			let Some (exn0, tmn0) = result.(srcidx)
			in
			let (dg1, Right (exectrue, execfalse), timenode') = convertTask btask {prep with atprocstart = false} !moddg exn0 tmn0
			in
			let (dg2, execaftertrue, timeaftertrue) = convertStoppingProcWork bnetedges.(trueidx) {prep with atprocstart = false} dg1 exectrue timenode'
			in
			let (dg3, execafterfalse, timeafterfalse) = convertStoppingProcWork bnetedges.(falseidx) {prep with atprocstart = false} dg2 execfalse timenode'
			in
			moddg := dg3;
			result.(trueidx) <- Some (execaftertrue, timeaftertrue);
			result.(falseidx) <- Some (execafterfalse, timeafterfalse)
		| SPRNJoin (srcidxl, tgtidx) ->
			let execnodesl = List.map (fun srcidx -> let Some (exn,_) = result.(srcidx) in exn) srcidxl
			and timenodesl = List.map (fun srcidx -> let Some (_,tmn) = result.(srcidx) in tmn) srcidxl
			in
			let (dg1, execafter) = GrbInput.addNodesToGraph !moddg prep.currixt execnodesl nkOr (fun _ -> PortUnstrB)
			in
			let (dg2, timeafter) = GrbInput.addNodesToGraph dg1 prep.currixt timenodesl (nkMerge VInteger) (fun _ -> PortMulti VInteger)
			in
			let (dg3, execend, timeend) = convertStoppingProcWork bnetedges.(tgtidx) {prep with atprocstart = false} dg2 execafter timeafter
			in
			moddg := dg3;
			result.(tgtidx) <- Some (execend, timeend)
	) bnetnodes;
	(!moddg, Array.map (fun (Some x) -> x) result)
;;

let rec (convertBPMNwork : anyproc -> graphpreparationtype -> DG.t -> GrbInput.attrlocationtype -> GrbInput.attrlocationtype -> DG.t) = fun bproc prep currdg execnode timenode -> match bproc with
| PRStop stproc -> let (dg,_,_) = convertStoppingProcWork stproc prep currdg execnode timenode in dg
| PRSeq (pr1, pr2) ->
	 let (dg1,exn1,tim1) = convertStoppingProcWork pr1 prep currdg execnode timenode
	 in
	 convertBPMNwork pr2 {prep with atprocstart = false} dg1 exn1 tim1
| PRParal prlist -> List.fold_right (fun prx dg -> convertBPMNwork prx {prep with atprocstart = false} dg execnode timenode) prlist currdg
| PRBranch (booltask, truebranch, falsebranch) ->
	let (dg0, Right (exectrue, execfalse), timenode') = convertTask booltask {prep with atprocstart = false} currdg execnode timenode
	in
	let dg1 = convertBPMNwork truebranch {prep with atprocstart = false} dg0 exectrue timenode'
	in
	convertBPMNwork falsebranch {prep with atprocstart = false} dg1 execfalse timenode'
| PRNetwork (spredges, sprnodes, prends) ->
	let (dg0, allends) = convertStoppingProcNetwork spredges sprnodes prep currdg execnode timenode
	in
	List.fold_right (fun (stidx, prx) dg -> let (exn,tmn) = allends.(stidx) in convertBPMNwork prx {prep with atprocstart = false} dg exn tmn) prends dg0
| PRReplicate (replproc, rprname) ->
	let AITT ixtcont = prep.currixt
	in
	let projmap = IxM [| Some ((), 0, Array.init (Array.length ixtcont.(0)) (fun x -> x)) |]
	in
	let newixt = AITT [| Array.append ixtcont.(0) [| (VInteger, Some rprname) |]  |]
	in
	let (dg1, replexecnode) = GrbInput.putIdNodeOnTop currdg execnode prep.currixt newixt projmap
	in
	let (dg2, repltimenode) = GrbInput.putIdNodeOnTop dg1 timenode prep.currixt newixt projmap
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
	convertBPMNwork replproc newprep dg2 replexecnode repltimenode
;;

let (convertBPMN : anyproc -> datasetdeclaration list -> RLSet.t -> DG.t) = fun bproc datasetdefs inpdatasets ->
	let oc = open_out "procdescr"
	in
	printanyproc oc 0 bproc;
	close_out oc;
	let dg0 = DG.empty
	and mydatasetdecls = List.fold_right (fun (dsname, dsdesc) m -> RLMap.add dsname (dsname, dsdesc) m) datasetdefs RLMap.empty
	and zeroixt = AITT [| [||] |]
	in
	let persistentDescs = collectPersistentDatasetsProc bproc [] RLMap.empty
	in
	let persistentSet = RLMap.fold (fun dsname _ s -> RLSet.add dsname s) persistentDescs RLSet.empty
	in
	let (dslocs, dg1) = findBPDataSets bproc mydatasetdecls inpdatasets persistentSet zeroixt dg0
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
	let (dg4, execnode) = GrbInput.addNodesToGraph dg3 zeroixt [] nkTrue (fun _ -> PortSingleB)
	in
	let (dg5, timenode) = GrbInput.addNodesToGraph dg4 zeroixt [] (nkOperation 0 VInteger (OPIntConst 0)) (fun _ -> PortSingle VInteger)
	in
	convertBPMNwork bproc prep dg5 execnode timenode
;;

