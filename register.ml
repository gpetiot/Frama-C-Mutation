
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


(*
let run_pcva =
  Dynamic.get ~plugin:"PrePC" "run"
    (Datatype.func Datatype.unit Datatype.unit)
*)


let run() =
  if Options.Enabled.get() then
    let funcname = Kernel_function.get_name (fst (Globals.entry_point())) in
    let () = Visitor.visitFramacFile
      (new gather_mutations funcname :> Visitor.frama_c_inplace) (Ast.get()) in
    if List.length !mutations = 0 then
      Options.Self.feedback "aucune mutation"
    else
      let trace = ref [] in
      let all_mutants_cpt = ref 0 in
      let killed_mutants_cpt = ref 0 in
      let recap = ref ["|      | Killed |   Not  |"] in
      let () = Options.Self.feedback "%i mutants" (List.length !mutations) in
      let rec mutate cpt = function
	| [] -> ()
	| h::t ->
	  let prj4 =
	    File.create_project_from_visitor ("__mut"^(string_of_int cpt))
	      (fun p -> new mutation_visitor p h funcname) in
	  let () = Project.copy ~selection:(Plugin.get_selection()) prj4 in
	  let () = Project.on prj4 (fun () ->
	    let () = Options.Self.feedback "mutant %i" cpt in
	    let () = Globals.set_entry_point funcname false in
	    let filename = "mutant_"^(string_of_int cpt)^".c" in
	    let chan = open_out filename in
	    let fmt = Format.formatter_of_out_channel chan in
	    let () = File.pretty_ast ~fmt () in
	    let () = flush chan in
	    let () = close_out chan in
	    let pc_options = "-pc-no-xml -pc-no-drivers" in
	    let werror_options = "-werror-no-unknown -werror-no-external" in
	    let cmd =
	      Printf.sprintf
		"frama-c %s -main %s -no-unicode -val -rte -then -prepc %s -then -werror %s > /dev/null 2>&1"
		filename funcname pc_options werror_options in
	    let ret = Sys.command cmd in
(*
	    let () = run_pcva () in
	    let bo = Property_status.fold (fun prop b ->
	      b && match Property_status.get prop with
	      | Property_status.Best (Property_status.False_and_reachable,_)
	      | Property_status.Best (Property_status.False_if_reachable,_) ->
		false
	      | _ -> true ) true
	    in
	    if bo then
*)
	    let str = Printf.sprintf "| %4i |   %c    |   %c    | %s" cpt
	      (if ret = 0 then ' ' else 'X')
	      (if ret = 0 then 'X' else ' ')
	      (mutation_to_string h)
	    in
	    recap := "--------------------------" :: str :: !recap;
	    if ret <> 0 then
	      let () = killed_mutants_cpt := !killed_mutants_cpt +1 in
	      trace :=
		(Printf.sprintf "%s (%s)"
		   (mutation_to_string h) filename) :: !trace
	  ) () in
	  (*let () = Project.remove ~project:prj4 () in*)
	  let () = all_mutants_cpt := !all_mutants_cpt + 1 in
	  mutate (cpt+1) t in
      let () = mutate 0 (List.rev !mutations) in
      let () = List.iter (fun s -> Options.Self.debug ~level:2 "%s" s) !trace in
      let recap = List.rev !recap in
      let () = List.iter (fun s -> Options.Self.feedback "%s" s) recap in
      let () = Options.Self.result "%i mutants" !all_mutants_cpt in
      let () = Options.Self.result "%i mutants killed" !killed_mutants_cpt in
      mutations := []
	
	
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "MUT" deps run in
  f
    
let() = Db.Main.extend run
  
