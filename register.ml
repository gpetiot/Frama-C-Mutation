
open Cil_types


type mutation =
  | Int_Arith of binop * binop * location (* PlusA, MinusA, Mult, Div, Mod *)
  | Ptr_Arith of binop * binop * location (* PlusPI, IndexPI,  MinusPI *)
  | Logic_And_Or of binop * binop * location (* LAnd, LOr *)
  | Comp of binop * binop * location (* Lt, Gt, Le, Ge, Eq, Ne *)
  | Mut_Lval of lval * lval * location
  | Cond of exp * exp * location
  | Free of stmt * location


module Mutation = struct
  let pretty fmt = function
  | Int_Arith(b1,b2,loc)
  | Ptr_Arith(b1,b2,loc)
  | Logic_And_Or(b1,b2,loc)
  | Comp(b1,b2,loc) ->
    Format.fprintf fmt "%a: (%a) --> (%a)"
      Printer.pp_location loc
      Printer.pp_binop b1
      Printer.pp_binop b2
  | Mut_Lval(l1,l2,loc) ->
    Format.fprintf fmt "%a: %a --> %a"
      Printer.pp_location loc
      Printer.pp_lval l1
      Printer.pp_lval l2
  | Cond(e1,e2,loc) ->
    Format.fprintf fmt "%a: %a --> %a"
      Printer.pp_location loc
      Printer.pp_exp e1
      Printer.pp_exp e2
  | Free(s,loc) ->
    Format.fprintf fmt "%a: %a"
      Printer.pp_location loc
      Printer.pp_stmt s
end


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
let rec compat_types t1 t2 =
  match (t1, t2) with
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


class gatherer funcname = object(self)
  inherit Visitor.frama_c_inplace

  val blocks:(block Stack.t) = Stack.create()
  val mutable mutations = []

  method! vblock block =
    let _ = Stack.push block blocks in
    Cil.ChangeDoChildrenPost (block, (fun b -> let _ = Stack.pop blocks in b))

  method! vexpr exp =
    let f e =
      let loc = e.eloc in
      let () = match e.enode with
	| BinOp (op, _, _, _) ->
	  begin
	    try
	      if option_of_binop op then
		List.iter
		  (fun o -> mutations <- binop_mutation op o loc :: mutations)
		  (other_binops op)
	    with _ -> ()
	  end
	| Lval ((Var vi,offset) as lv) ->
	  if Options.Mutate_Lval.get() then
	    let vars = (Stack.top blocks).blocals in
	    let vars =
	      match self#current_kf with
	      | Some {fundec=Definition(d,_)} -> List.rev_append d.sformals vars
	      | _ -> vars
	    in
	    let other_vars = List.filter
	      (fun x -> x.vid <> vi.vid && compat_types x.vtype vi.vtype)
	      vars
	    in
	    List.iter
	      (fun v ->
		mutations <- Mut_Lval(lv,(Var v, offset),loc) :: mutations)
	      other_vars
	| _ -> ()
      in
      e
    in
    Cil.ChangeDoChildrenPost (exp, f)

  method! vstmt_aux stmt =
    if stmt.ghost then
      Cil.SkipChildren
    else
      let f s =
	let () = 
	  match s.skind with
	  | Instr(Call(_, {eloc=loc;enode=Lval(Var{vname="free"}, _)}, _, _)) ->
	    if Options.Mutate_Free.get() then
	      mutations <- Free(s,loc) :: mutations
	  | If (exp, _b1, _b2, loc) ->
	    if Options.Mutate_Cond.get() then
	      let new_bool = Cil.new_exp loc (UnOp (LNot, exp, Cil.intType)) in
	      mutations <- Cond(exp, new_bool, loc) :: mutations
	  | _ -> ()
	in
	s
      in
      Cil.ChangeDoChildrenPost (stmt, f)

  method! vglob_aux glob =
    match glob with
    | GFun (f,_) when f.svar.vname <> (funcname^"_precond") ->
      Cil.ChangeDoChildrenPost ([glob], (fun x -> x))
    | _ -> Cil.SkipChildren

  method get_mutations() = mutations
end


let same_locs l1 l2 = (Cil_datatype.Location.compare l1 l2) = 0


class mutation_visitor prj mut name = object
  inherit Visitor.frama_c_copy prj

  method! vexpr exp =
    let f e =
      match (e.enode, mut) with
      | BinOp (_, e1, e2, ty), Int_Arith (_, b2, l)
      | BinOp (_, e1, e2, ty), Ptr_Arith (_, b2, l)
      | BinOp (_, e1, e2, ty), Logic_And_Or (_, b2, l)
      | BinOp (_, e1, e2, ty), Comp (_, b2, l) when same_locs e.eloc l ->
	Cil.new_exp e.eloc (BinOp (b2, e1, e2, ty))
      | Lval _, Mut_Lval (_, v, l) when same_locs e.eloc l ->
	Cil.new_exp e.eloc (Lval v)
      | _ -> e
    in
    Cil.ChangeDoChildrenPost (exp, f)

  method! vstmt_aux stmt =
    let f s =
      match (s.skind, mut) with
      |(Instr(Call(_,{eloc=loc;enode=Lval(Var{vname="free"},_)},_,_)),Free(_,l))
	  when same_locs loc l -> Cil.mkStmtCfgBlock []
      | (If (e, b1, b2, loc), Cond (_, _, l)) when same_locs loc l ->
	let new_e = Cil.new_exp loc (UnOp (LNot, e, Cil.intType)) in
	{s with skind = If (new_e, b1, b2, loc)}
      | _ -> s
    in
    Cil.ChangeDoChildrenPost (stmt, f)
end


(*
let run_stady =
  Dynamic.get ~plugin:"stady" "run_stady"
    (Datatype.func Datatype.unit Datatype.unit)
*)


let run() =
  if Options.Enabled.get() then
    let funcname = Kernel_function.get_name (fst (Globals.entry_point())) in
    let mutation_gatherer = new gatherer funcname in
    Visitor.visitFramacFile
      (mutation_gatherer :> Visitor.frama_c_inplace) (Ast.get());
    let mutations = mutation_gatherer#get_mutations() in
    let killed_mutants_cpt = ref 0 in
    Options.Self.feedback "%i mutants" (List.length mutations);
    let rec mutate cpt recap = function
      | [] -> recap
      | _ when Options.Only.get() <> -1 && Options.Only.get() < cpt ->
	recap
      | _::t when Options.Only.get() <> -1 && Options.Only.get() > cpt ->
	mutate (cpt+1) recap t
      | h::t ->
	let filename = "mutant_"^(string_of_int cpt)^".c" in
	Options.Self.feedback "mutant %i %a" cpt Mutation.pretty h;
	let prj4 =
	  File.create_project_from_visitor ("__mut"^(string_of_int cpt))
	    (fun p -> new mutation_visitor p h funcname) in
	Project.copy ~selection:(Parameter_state.get_selection()) prj4;
	let ret = Project.on prj4 (fun () ->
	  Globals.set_entry_point funcname false;
	  let chan = open_out filename in
	  let fmt = Format.formatter_of_out_channel chan in
	  File.pretty_ast ~fmt ();
	  flush chan;
	  close_out chan;
	  let cmd =
	    Printf.sprintf "frama-c %s -main %s -no-unicode \
-rte \
-then -stady \
-then -werror -werror-no-unknown -werror-no-external"
	      filename funcname in
	  let ret = (Sys.command cmd) = 0 in

	  (*
	    !Db.RteGen.compute();
	    !Db.Value.compute();
	    run_stady ();
	    let ret = Property_status.fold (fun prop b ->
	    b && match Property_status.get prop with
	    | Property_status.Best (Property_status.False_and_reachable,_) ->
	    false
	    | _ -> true ) true
	    in
	  *)

	  ret
	) ()
	in
	if not ret then
	  killed_mutants_cpt := !killed_mutants_cpt +1;

	Options.Self.debug ~level:2 "%a (%s)" Mutation.pretty h filename;
	Project.remove ~project:prj4 ();
	mutate (cpt+1) ((cpt, ret, h) :: recap) t
    in
    let recap = mutate 0 [] mutations in

    
    Options.Self.feedback "|      | Killed |   Not  |";
    List.iter (fun (i,r,m) ->
      Options.Self.feedback "| %4i |   %c    |   %c    | %a"
	i (if r then ' ' else 'X') (if r then 'X' else ' ') Mutation.pretty m;
      Options.Self.feedback "--------------------------"
    ) recap;
    Options.Self.result "%i mutants" (List.length mutations);
    Options.Self.result "%i mutants killed" !killed_mutants_cpt
	
	
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "MUT" deps run in
  f
    
let() = Db.Main.extend run
