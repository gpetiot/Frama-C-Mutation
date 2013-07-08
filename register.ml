
open Cil
open Cil_types
open Lexing



type mutation =
  | Int_Arith of binop * binop * location (* PlusA, MinusA, Mult, Div, Mod *)
  | Ptr_Arith of binop * binop * location (* PlusPI, IndexPI,  MinusPI *)
  | Logic_And_Or of binop * binop * location (* LAnd, LOr *)
  | Comp of binop * binop * location (* Lt, Gt, Le, Ge, Eq, Ne *)
  | Mut_Lval of lval * lval * location
  | Cond of exp * exp * location
  | Free of stmt * location

(* mutation -> string *)
let mutation_to_string = function
  | Int_Arith(b1,b2,loc)
  | Ptr_Arith(b1,b2,loc)
  | Logic_And_Or(b1,b2,loc)
  | Comp(b1,b2,loc) ->
    Pretty_utils.sfprintf "%a: (%a) --> (%a)" Printer.pp_location loc
      Printer.pp_binop b1 Printer.pp_binop b2
  | Mut_Lval(l1,l2,loc) ->
    Pretty_utils.sfprintf "%a: %a --> %a" Printer.pp_location loc
      Printer.pp_lval l1 Printer.pp_lval l2
  | Cond(e1,e2,loc) ->
    Pretty_utils.sfprintf "%a: %a --> %a" Printer.pp_location loc
      Printer.pp_exp e1 Printer.pp_exp e2
  | Free(s,loc) ->
    Pretty_utils.sfprintf "%a: %a" Printer.pp_location loc Printer.pp_stmt s

(* determine what can binary operators be mutated into *)
(* binop -> binop list *)
let other_binops = function
  | PlusA -> [MinusA;Mult;Div;Mod]
  | MinusA -> [PlusA;Mult;Div;Mod]
  | Mult -> [Div;Mod;PlusA;MinusA]
  | Div -> [Mult;Mod;PlusA;MinusA]
  | Mod -> [Mult;Div;PlusA;MinusA]
  | PlusPI | IndexPI -> [MinusPI]
  | MinusPI -> [PlusPI]
  | LAnd -> [LOr]
  | LOr -> [LAnd]
  | Lt -> [Le;Gt;Ge;Eq;Ne]
  | Gt -> [Ge;Lt;Le;Eq;Ne]
  | Le -> [Gt;Ge;Eq;Ne;Lt]
  | Ge -> [Lt;Le;Eq;Ne;Gt]
  | Eq -> [Ne]
  | Ne -> [Eq]
  | _ -> failwith "other_binops"

(* binop -> bool *)
let option_of_binop = function
  | PlusA | MinusA | Mult | Div | Mod -> Options.Mutate_Int_Arith.get()
  | PlusPI | IndexPI | MinusPI -> Options.Mutate_Ptr_Arith.get()
  | LAnd | LOr -> Options.Mutate_Logic_And_Or.get()
  | Lt | Gt | Le | Ge | Eq | Ne -> Options.Mutate_Comp.get()
  | _ -> failwith "option_of_binop"

(* binop -> binop -> location -> mutation *)
let binop_mutation op1 op2 loc =
  match op1 with
    | PlusA | MinusA | Mult | Div | Mod -> Int_Arith(op1,op2,loc)
    | PlusPI | IndexPI | MinusPI -> Ptr_Arith(op1,op2,loc)
    | LAnd | LOr -> Logic_And_Or(op1,op2,loc)
    | Lt | Gt | Le | Ge | Eq | Ne -> Comp(op1,op2,loc)
    | _ -> failwith "constr_binop"

(* used to mutate a lvalue into another one with (quite) compatible type *)
(* typ -> typ -> bool *)
let rec compat_types t1 t2 = match (t1, t2) with
  | TVoid _, TVoid _
  | TInt _, TInt _
  | TFloat _, TFloat _
  | TInt _, TFloat _
  | TFloat _, TInt _ -> true
  | TFun (p1, _, _, _), TFun (p2, _, _, _)
  | TPtr (p1, _), TPtr (p2, _)
  | TArray (p1, _, _, _), TArray (p2, _, _, _) -> compat_types p1 p2
  | TNamed ({ttype=ty}, _), k
  | k, TNamed ({ttype=ty}, _) -> compat_types ty k
  | _ -> false





let mutations = ref ([]: mutation list)

(* mutation -> unit *)
let gather_mutation m =
  let () = mutations := m::!mutations in
  Options.Self.debug ~level:2 "%s" (mutation_to_string m)


class gather_mutations funcname = object(self)
  inherit Visitor.frama_c_inplace

  val blocks:(block Stack.t) = Stack.create()

  method vblock block =
    let _ = Stack.push block blocks in
    ChangeDoChildrenPost (block, (fun b -> let _ = Stack.pop blocks in b))

  method vexpr exp =
    let f e =
      let loc = e.eloc in
      let () = match e.enode with
	| BinOp (op, _, _, _) ->
	  begin
	    try
	      if option_of_binop op then
		List.iter
		  (fun o -> gather_mutation (binop_mutation op o loc))
		  (other_binops op)
	    with
	      | _ -> ()
	  end
	| Lval ((Var vi,offset) as lv) ->
	  if Options.Mutate_Lval.get() then
	    let all_vars = (Stack.top blocks).blocals in
	    let all_vars = match self#current_kf with
	      | Some {fundec=Declaration _} -> all_vars
	      | Some {fundec=Definition(fundec,_)} ->
		List.rev_append fundec.sformals all_vars
	      | _ -> all_vars in
	    let other_vars = List.filter
	      (fun x -> x.vid <> vi.vid && compat_types x.vtype vi.vtype)
	      all_vars in
	    List.iter
	      (fun v -> gather_mutation (Mut_Lval(lv,(Var v, offset),loc)))
	      other_vars
	| _ -> () in e
    in ChangeDoChildrenPost (exp, f)

  method vstmt_aux stmt =
    if stmt.ghost then
      SkipChildren
    else
      let f s =
	let () = 
	  match s.skind with
	  | Instr(Call(_, {eloc=loc;enode=Lval(Var{vname="free"}, _)}, _, _)) ->
	    if Options.Mutate_Free.get() then gather_mutation (Free(s,loc))
	  | If (exp, _b1, _b2, loc) ->
	    if Options.Mutate_Cond.get() then
	      let new_bool = new_exp loc (UnOp (LNot, exp, intType)) in
	      gather_mutation (Cond(exp, new_bool, loc))
	  | _ -> ()
	in s
      in ChangeDoChildrenPost (stmt, f)

  method vglob_aux glob =
    match glob with
    | GFun (f,_) when f.svar.vname <> (funcname^"_precond") ->
      ChangeDoChildrenPost ([glob], (fun x -> x))
    | _ -> SkipChildren
end



class mutation_visitor prj mut name = object
  inherit Visitor.frama_c_copy prj

  method vglob_aux glob =
    match glob with
      | GFun (f, loc) when f.svar.vname = name ->
	ChangeDoChildrenPost
	  ([glob], fun x -> (GFun(emptyFunction "main", loc))::x)
      | GFun _ -> ChangeDoChildrenPost ([glob], (fun x -> x))
      | _ -> JustCopy

  method vexpr exp =
    let f e =
      let loc = e.eloc in
      match (e.enode, mut) with
	| BinOp (_, e1, e2, ty), Int_Arith (_, b2, l)
	| BinOp (_, e1, e2, ty), Ptr_Arith (_, b2, l)
	| BinOp (_, e1, e2, ty), Logic_And_Or (_, b2, l)
	| BinOp (_, e1, e2, ty), Comp (_, b2, l)
	  when (Cil_datatype.Location.compare loc l) = 0 ->
	  new_exp ~loc (BinOp (b2, e1, e2, ty))
	| Lval _, Mut_Lval (_, v2, l)
	  when (Cil_datatype.Location.compare loc l) = 0 ->
	  new_exp ~loc (Lval v2)
	| _ -> copy_exp e in
    ChangeDoChildrenPost (exp, f)

  method vstmt_aux stmt =
    let f s =
      match (s.skind, mut) with
	| (Instr(Call(_, {eloc=loc;enode=Lval(Var{vname="free"}, _)}, _, _)),
	   Free (_, l))
	    when (Cil_datatype.Location.compare loc l) = 0 -> mkStmtCfgBlock []
	| (If (_, b1, b2, loc), Cond (_, e2, l))
	    when (Cil_datatype.Location.compare loc l) = 0 ->
	  mkStmt (If (e2, b1, b2, loc))
	| _ -> s in
    ChangeDoChildrenPost (stmt, f)
end


class keep_only_main prj name = object
  inherit Visitor.frama_c_copy prj
  method vglob_aux = function
    | GFun (f,_) when f.svar.vname = "main"
		 || f.svar.vname = "e_acsl_global_init" -> JustCopy
    | GFun (f,loc) when f.svar.vname = name
		   || f.svar.vname = "__e_acsl_" ^ name ->
      ChangeTo [GVarDecl(f.sspec,f.svar,loc)]
    | _ -> ChangeTo []
end

class delete_main prj = object
  inherit Visitor.frama_c_copy prj
  method vglob_aux = function
    | GFun (f,_) when f.svar.vname = "main" -> ChangeTo []
    | _ -> JustCopy
end

class fix_malloc_free = object
  inherit Visitor.frama_c_inplace

  method vstmt_aux stmt =
    let f s =
      match s.skind with
      | Instr(Call(_, {eloc=_;enode=Lval(Var vi, _)}, _, _)) ->
	(if vi.vname = "__e_acsl_malloc" then vi.vname <- "__malloc"
	else if vi.vname = "__e_acsl_free" then vi.vname <- "__free"
	else if vi.vname = "__e_acsl_realloc" then vi.vname <- "__realloc"
	else if vi.vname = "__e_acsl_calloc" then vi.vname <- "__calloc"
	else ()); s
      | _ -> s
    in ChangeDoChildrenPost (stmt, f)
end

class skip_clean = object
  inherit Visitor.frama_c_inplace

  method vstmt_aux stmt =
    let f s =
      match s.skind with
      | Instr (Call(_, {eloc=l;enode=Lval(Var vi, _)},_,_)) ->
	if vi.vname = "__clean" then mkStmtOneInstr (Skip l)
	else s
      | _ -> s
    in ChangeDoChildrenPost (stmt, f)
end


let generate_code =
  Dynamic.get ~plugin:"E_ACSL" "generate_code"
    (Datatype.func Datatype.string Project.ty)


let run() =
  if Options.Enabled.get() then
    let funcname = Kernel_function.get_name (fst (Globals.entry_point())) in
    let () = Visitor.visitFramacFile
      (new gather_mutations funcname :> Visitor.frama_c_inplace) (Ast.get()) in
    if List.length !mutations = 0 then
      Options.Self.feedback "aucune mutation"
    else
      let files = Kernel.Files.get() in
      let first_file = List.hd files in
      let files = List.fold_left (fun a b -> a ^ " " ^ b) "" files in
      let _ =
	Sys.command
	  (Printf.sprintf
	     "frama-c %s -main %s -pc -pc-verbose 0 -kernel-verbose 0"
	     files funcname) in
      let testdrivers_dir = Filename.dirname (List.hd (Kernel.Files.get())) in
      let testdrivers_dir = Filename.concat testdrivers_dir
	("testcases_"^
	    (Filename.chop_extension (Filename.basename (first_file)))) in
      let testdrivers_dir = Filename.concat testdrivers_dir funcname in
      let testdrivers_dir = Filename.concat testdrivers_dir "testdrivers" in
      let testdrivers = Array.to_list (Sys.readdir testdrivers_dir) in
      let testdrivers = List.filter (fun s -> Filename.check_suffix s ".c")
	testdrivers in
      let lanceur_params = "pathcrawler_"^
	(Filename.chop_extension (Filename.basename first_file)) in
      let lanceur_params = Filename.concat lanceur_params
	("lanceur_"^funcname^"_params.h") in
      let params_file = open_in lanceur_params in
      let rec aux ret =
	try
	  let s = input_line params_file in aux (ret^" "^s^"\n")
	with
	    End_of_file -> ret in
      let params = aux "" in
      let () = close_in params_file in
      let () = List.iter (fun f ->
	let complete_name = Filename.concat testdrivers_dir f in
	let file = File.from_filename complete_name in
	let prj = Project.create "__mut1" in
	let () = Project.copy
	  ~selection:(State_selection.of_list
			[Kernel.Machdep.self; Kernel.CppExtraArgs.self]) prj in
	let () = Project.on prj (fun () -> File.init_from_c_files [file]) () in
	let prj2 = Project.on prj (fun () ->
	  Globals.set_entry_point "main" false;
	  generate_code "__mut2") () in
	let prj3 = Project.on prj2 (fun () ->
	  File.create_project_from_visitor "__mut3"
	    (fun p -> new keep_only_main p funcname)) () in
	let () = Project.on prj3 (fun () -> Visitor.visitFramacFile
	  (new fix_malloc_free :> Visitor.frama_c_inplace) (Ast.get())) () in
	let chan = open_out ((Filename.chop_extension complete_name)^".i") in
	let () = output_string chan params in
	let () = output_string chan "extern void __clean();\n" in
	let () = output_string chan "extern void* __malloc(unsigned int);\n" in
	let () = output_string chan "extern void __initialize(void*,int);\n" in
	let () = output_string chan "extern void __free(void* );\n" in
	let () = output_string chan "extern void __full_init(void* );\n" in
	let () = output_string chan "extern void __delete_block(void* );\n" in
	let () = output_string chan "extern void __store_block(void*,int);\n" in
	let fmt = Format.formatter_of_out_channel chan in
	let () = Project.on prj3 (fun () -> File.pretty_ast ~fmt ()) () in
	let () = flush chan in
	let () = close_out chan in
	List.iter (fun p -> Project.on p (fun () -> Project.remove()) ())
	  [prj;prj2;prj3]
      ) testdrivers in
      let testdrivers = List.map (fun t ->
	(Filename.chop_extension (Filename.concat testdrivers_dir t))^".i"
      ) testdrivers in
      let eacsldir = "~/e-acsl/share/e-acsl" in
      let trace = ref [] in
      let all_mutants_cpt = ref 0 in
      let killed_mutants_cpt = ref 0 in
      let mutants_not_killed = ref [] in

      (********************)
      let () = Globals.set_entry_point "main" false in
      let prj5 = generate_code "__mut5" in
      let () = Project.set_current prj5 in
      let prj6 = File.create_project_from_visitor "__mut6"
	(fun p -> new delete_main p) in
      let () = Project.on prj6 (fun () -> Visitor.visitFramacFile
	(new skip_clean :> Visitor.frama_c_inplace) (Ast.get())) () in
      let () = Project.set_current prj6 in
      let filename = "orig.c" in
      let chan = open_out filename in
      let fmt = Format.formatter_of_out_channel chan in
      let () = File.pretty_ast ~fmt () in
      let () = flush chan in
      let () = close_out chan in
      let () = List.iter (fun p -> Project.remove ~project:p ()) [prj5;prj6] in
      let rec test = function
	| [] -> ()
	| testdriver::t ->
	  let execname =
	    (Filename.chop_extension (Filename.basename testdriver))
	    ^"_"^"orig.out" in
	  let opt = "-pedantic -Wno-long-long -Wno-attributes -fno-builtin" in
	  let cmd = Printf.sprintf
	    "gcc -std=c99 %s -o %s %s %s %s/*.c %s/memory_model/*.c && ./%s"
	    opt execname filename testdriver eacsldir eacsldir execname in
	  let ret = Sys.command cmd in
	  if ret = 1 then
	    let () = Options.Self.result "[KO] %s & %s" filename testdriver in
	    failwith "orig fails!"
	  else
	    test t
      in
      let () = test testdrivers in
      (********************)

      let rec mutate cpt = function
	| [] -> ()
	| h::t ->
	  let prj4 = File.create_project_from_visitor "__mut4"
	    (fun p -> new mutation_visitor p h funcname) in
	  let () = Project.set_current prj4 in
	  let () = Globals.set_entry_point funcname false in
	  let () = !Db.RteGen.compute() in
	  let () = Globals.set_entry_point "main" false in
	  let prj5 = generate_code "__mut5" in
	  let () = Project.set_current prj5 in
	  let prj6 = File.create_project_from_visitor "__mut6"
	    (fun p -> new delete_main p) in
	  let () = Project.on prj6 (fun () -> Visitor.visitFramacFile
	    (new skip_clean :> Visitor.frama_c_inplace) (Ast.get())) () in
	  let () = Project.set_current prj6 in
	  let filename = "mutant_"^(string_of_int cpt)^".c" in
	  let chan = open_out filename in
	  let fmt = Format.formatter_of_out_channel chan in
	  let () = File.pretty_ast ~fmt () in
	  let () = flush chan in
	  let () = close_out chan in
	  let () = List.iter (fun p -> Project.remove ~project:p ())
	    [prj4;prj5;prj6] in
	  let () = all_mutants_cpt := !all_mutants_cpt + 1 in
	  let rec test = function
	    | [] -> mutants_not_killed := (cpt, h) :: !mutants_not_killed
	    | testdriver::t ->
	      let execname =
		(Filename.chop_extension (Filename.basename testdriver))
		^"_"^"mutant_"^(string_of_int cpt)^".out" in
	      let opt="-pedantic -Wno-long-long -Wno-attributes -fno-builtin" in
	      let files = Printf.sprintf "%s %s %s/*.c %s/memory_model/*.c"
		filename testdriver eacsldir eacsldir in
	      let exec_cmd = "~/timeout3 -t 5" in
	      let cmd = Printf.sprintf "gcc -std=c99 %s -o %s %s && %s ./%s"
		opt execname files exec_cmd execname in
	      let () = Options.Self.debug ~level:2 "%s + %s"
		filename testdriver in
	      let ret = Sys.command cmd in
	      if ret = 1 then
		killed_mutants_cpt := !killed_mutants_cpt +1
	      else
		let () =
		  trace :=
		    (Printf.sprintf "%s (%s) & %s"
		       (mutation_to_string h) filename testdriver) :: !trace in
		test t
	  in
	  let () = test testdrivers in
	  mutate (cpt+1) t in
      let () = mutate 0 (List.rev !mutations) in
      let () = List.iter (fun s -> Options.Self.debug ~level:2 "%s" s) !trace in
      let () = Options.Self.result "%i test cases" (List.length testdrivers) in
      let () = Options.Self.result "%i mutants" !all_mutants_cpt in
      let () = Options.Self.result "%i mutants killed" !killed_mutants_cpt in
      Options.Self.result "%i not killed" (List.length !mutants_not_killed);
      List.iter
	(fun (i, m) -> Options.Self.result "%i: %s" i (mutation_to_string m))
	!mutants_not_killed;
      mutations := []
	
	
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "MUT" deps run in
  f
    
let() = Db.Main.extend run
  
