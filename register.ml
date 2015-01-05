
open Cil_types


type mutation =
  | Int_Arith of binop * binop * location (* PlusA, MinusA, Mult, Div, Mod *)
  | Ptr_Arith of binop * binop * location (* PlusPI, IndexPI, MinusPI *)
  | Logic_And_Or of binop * binop * location (* LAnd, LOr *)
  | Comp of binop * binop * location (* Lt, Gt, Le, Ge, Eq, Ne *)
  | Cond of exp * exp * location


let pp_mutation fmt = function
  | Int_Arith(b1,b2,loc)
  | Ptr_Arith(b1,b2,loc)
  | Logic_And_Or(b1,b2,loc)
  | Comp(b1,b2,loc) -> Format.fprintf fmt "%a: (%a) --> (%a)"
    Printer.pp_location loc
    Printer.pp_binop b1
    Printer.pp_binop b2
  | Cond(e1,e2,loc) -> Format.fprintf fmt "%a: %a --> %a"
    Printer.pp_location loc
    Printer.pp_exp e1
    Printer.pp_exp e2


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
  | _ -> assert false

let option_of_binop = function
  | PlusA | MinusA | Mult | Div | Mod -> Options.Mutate_Int_Arith.get()
  | PlusPI | IndexPI | MinusPI -> Options.Mutate_Ptr_Arith.get()
  | LAnd | LOr -> Options.Mutate_Logic_And_Or.get()
  | Lt | Gt | Le | Ge | Eq | Ne -> Options.Mutate_Comp.get()
  | _ -> assert false

let binop_mutation op1 op2 loc = match op1 with
  | PlusA | MinusA | Mult | Div | Mod -> Int_Arith(op1,op2,loc)
  | PlusPI | IndexPI | MinusPI -> Ptr_Arith(op1,op2,loc)
  | LAnd | LOr -> Logic_And_Or(op1,op2,loc)
  | Lt | Gt | Le | Ge | Eq | Ne -> Comp(op1,op2,loc)
  | _ -> assert false


class gatherer funcname = object(self)
  inherit Visitor.frama_c_inplace

  val mutable mutations = []

  method get_mutations() = mutations
  method private add m = mutations <- m :: mutations

  method! vexpr exp = match exp.enode with
  | BinOp((PlusA|MinusA|Mult|Div|Mod|PlusPI|IndexPI|MinusPI|LAnd|LOr|Lt|Gt|Le
	      |Ge|Eq|Ne) as op, _, _, _) when option_of_binop op ->
    let add o = self#add (binop_mutation op o exp.eloc) in
    List.iter add (other_binops op);
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vstmt_aux stmt = match stmt.skind with
  | If (exp, _, _, loc) when Options.Mutate_Cond.get() ->
    let new_bool = Cil.new_exp loc (UnOp (LNot, exp, Cil.intType)) in
    self#add (Cond(exp, new_bool, loc));
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vglob_aux glob = match glob with
  | GFun (f,_) when f.svar.vname = (funcname ^ "_precond") -> Cil.SkipChildren
  | _ -> Cil.DoChildren
end


let same_locs l1 l2 = (Cil_datatype.Location.compare l1 l2) = 0


class mutation_visitor prj mut name = object
  inherit Visitor.frama_c_copy prj

  method! vexpr exp =
    let f e = match (e.enode, mut) with
      | BinOp (_, e1, e2, ty), Int_Arith (_, b2, l)
      | BinOp (_, e1, e2, ty), Ptr_Arith (_, b2, l)
      | BinOp (_, e1, e2, ty), Logic_And_Or (_, b2, l)
      | BinOp (_, e1, e2, ty), Comp (_, b2, l) when same_locs e.eloc l ->
	Cil.new_exp e.eloc (BinOp (b2, e1, e2, ty))
      | _ -> e
    in
    Cil.ChangeDoChildrenPost (exp, f)

  method! vstmt_aux stmt =
    let f s = match (s.skind, mut) with
      | (If (e, b1, b2, loc), Cond (_, _, l)) when same_locs loc l ->
	let new_e = Cil.new_exp loc (UnOp (LNot, e, Cil.intType)) in
	{s with skind = If (new_e, b1, b2, loc)}
      | _ -> s
    in
    Cil.ChangeDoChildrenPost (stmt, f)
end


let run() =
  if Options.Enabled.get() then
    let funcname = Kernel_function.get_name (fst (Globals.entry_point())) in
    let g = new gatherer funcname in
    Visitor.visitFramacFile (g :> Visitor.frama_c_inplace) (Ast.get());
    let mutations = g#get_mutations() in
    let killed_mutants_cpt = ref 0 in
    Options.Self.feedback "%i mutants" (List.length mutations);
    let rec mutate cpt recap = function
      | [] -> recap
      | _ when Options.Only.get() <> -1 && Options.Only.get() < cpt -> recap
      | _::t when Options.Only.get() <> -1 && Options.Only.get() > cpt ->
	mutate (cpt+1) recap t
      | h::t ->
	let filename = "mutant_"^(string_of_int cpt)^".c" in
	Options.Self.feedback "mutant %i %a" cpt pp_mutation h;
	let f p = new mutation_visitor p h funcname in
	let p_name = "__mut" ^ (string_of_int cpt) in
	let project = File.create_project_from_visitor p_name f in
	let cmd = Printf.sprintf "frama-c %s -main %s -no-unicode \
-rte -then -stady -then -werror -werror-no-unknown -werror-no-external"
	  filename funcname in
	Project.copy ~selection:(Parameter_state.get_selection()) project;
	let ret = Project.on project (fun () ->
	  Globals.set_entry_point funcname false;
	  let chan = open_out filename in
	  File.pretty_ast ~fmt:(Format.formatter_of_out_channel chan) ();
	  flush chan;
	  close_out chan;
	  (Sys.command cmd) = 0
	) ()
	in
	if not ret then killed_mutants_cpt := !killed_mutants_cpt +1;
	Options.Self.debug ~level:2 "%a (%s)" pp_mutation h filename;
	Project.remove ~project ();
	mutate (cpt+1) ((cpt, ret, h) :: recap) t
    in
    let recap = mutate 0 [] mutations in
    Options.Self.feedback "|      | Killed |   Not  |";
    List.iter (fun (i,r,m) ->
      Options.Self.feedback "| %4i |   %c    |   %c    | %a"
	i (if r then ' ' else 'X') (if r then 'X' else ' ') pp_mutation m;
      Options.Self.feedback "--------------------------"
    ) recap;
    Options.Self.result "%i mutants" (List.length mutations);
    Options.Self.result "%i mutants killed" !killed_mutants_cpt
	
	
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "MUT" deps run in
  f
    
let() = Db.Main.extend run
