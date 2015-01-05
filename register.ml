
open Cil_types


type mutation =
  (* mutations on code *)
  | Mut_BinOp of binop * binop * location
  | Mut_If of exp * exp * location
  (* mutations on spec *)
  | Mut_TBinOp of binop * binop * location
  | Mut_Prel of relation * relation * location


let pp_mutation fmt = function
  | Mut_TBinOp(b1,b2,loc)
  | Mut_BinOp(b1,b2,loc) -> Format.fprintf fmt "%a: (%a) --> (%a)"
    Printer.pp_location loc
    Printer.pp_binop b1
    Printer.pp_binop b2
  | Mut_If(e1,e2,loc) -> Format.fprintf fmt "%a: %a --> %a"
    Printer.pp_location loc
    Printer.pp_exp e1
    Printer.pp_exp e2
  | Mut_Prel(r1,r2,loc) -> Format.fprintf fmt "%a: (%a) --> (%a)"
    Printer.pp_location loc
    Printer.pp_relation r1
    Printer.pp_relation r2


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

let other_relations = function
  | Rlt -> [Rgt;Rle;Rge;Req;Rneq]
  | Rgt -> [Rlt;Rle;Rge;Req;Rneq]
  | Rle -> [Rlt;Rgt;Rge;Req;Rneq]
  | Rge -> [Rlt;Rgt;Rle;Req;Rneq]
  | Req -> [Rneq]
  | Rneq -> [Req]


let loc_ok (loc,_) =
  Filename.basename loc.Lexing.pos_fname <> "__fc_builtin_for_normalization.i"


class gatherer funcname = object(self)
  inherit Visitor.frama_c_inplace

  val mutable mutations = []

  method get_mutations() = mutations
  method private add m = mutations <- m :: mutations

  method! vpredicate_named p = match p.content with
  | Prel(r,_,_) when Options.Mut_Spec.get() && loc_ok p.loc ->
    let add o = self#add (Mut_Prel (r, o, p.loc)) in
    List.iter add (other_relations r);
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vterm t = match t.term_node with
  | TBinOp((PlusA|MinusA|Mult|Div|Mod|PlusPI|IndexPI|MinusPI|LAnd|LOr|Lt|Gt|Le
	      |Ge|Eq|Ne) as op, _, _)
      when Options.Mut_Spec.get() && loc_ok t.term_loc ->
    let add o = self#add (Mut_TBinOp (op, o, t.term_loc)) in
    List.iter add (other_binops op);
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vexpr exp = match exp.enode with
  | BinOp((PlusA|MinusA|Mult|Div|Mod|PlusPI|IndexPI|MinusPI|LAnd|LOr|Lt|Gt|Le
	      |Ge|Eq|Ne) as op, _, _, _) when Options.Mut_Code.get() ->
    let add o = self#add (Mut_BinOp (op, o, exp.eloc)) in
    List.iter add (other_binops op);
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vstmt_aux stmt = match stmt.skind with
  | If (exp, _, _, loc) when Options.Mut_Code.get() ->
    let new_bool = Cil.new_exp loc (UnOp (LNot, exp, Cil.intType)) in
    self#add (Mut_If(exp, new_bool, loc));
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vglob_aux glob = match glob with
  | GFun (f,_) when f.svar.vname = (funcname ^ "_precond") -> Cil.SkipChildren
  | _ -> Cil.DoChildren
end


let same_locs l1 l2 = (Cil_datatype.Location.compare l1 l2) = 0


class mutation_visitor prj mut name = object
  inherit Visitor.frama_c_copy prj

  method! vpredicate_named p = match p.content, mut with
  | Prel(r,x,y), Mut_Prel(w,z,l) when same_locs p.loc l && r = w ->
    Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (z,x,y))
  | _ -> Cil.DoChildren

  method! vterm term = match term.term_node, mut with
  | TBinOp(o,x,y), Mut_TBinOp(w,z,l) when same_locs term.term_loc l && o = w->
    Cil.ChangeDoChildrenPost
      (term, fun t -> Logic_const.term (TBinOp(z,x,y)) t.term_type)
  | _ -> Cil.DoChildren

  method! vexpr exp = match exp.enode, mut with
  | BinOp (o1,x,y,t), Mut_BinOp (o2,z,l) when same_locs exp.eloc l && o1 = o2 ->
    Cil.ChangeDoChildrenPost (exp, fun e -> Cil.new_exp e.eloc (BinOp(z,x,y,t)))
  | _ -> Cil.DoChildren

  method! vstmt_aux stmt = match stmt.skind, mut with
  | (If (e, x, y, loc), Mut_If (_, _, l)) when same_locs loc l ->
    let e = Cil.new_exp loc (UnOp (LNot, e, Cil.intType)) in
    Cil.ChangeDoChildrenPost (stmt, fun s -> {s with skind = If (e, x, y, loc)})
  | _ -> Cil.DoChildren
end


let rec mutate funcname cpt killed_mutants_cpt recap = function
  | [] -> killed_mutants_cpt, recap
  | _ when Options.Only.get() <> -1 && Options.Only.get() < cpt ->
    killed_mutants_cpt, recap
  | _::t when Options.Only.get() <> -1 && Options.Only.get() > cpt ->
    mutate funcname (cpt+1) killed_mutants_cpt recap t
  | h::t ->
    let filename = "mutant_" ^ (string_of_int cpt) ^ ".c" in
    let dkey = Options.dkey_progress in
    Options.Self.feedback ~dkey "mutant %i %a" cpt pp_mutation h;
    let f p = new mutation_visitor p h funcname in
    let project = File.create_project_from_visitor "__mut_tmp" f in
    Project.copy ~selection:(Parameter_state.get_selection()) project;
    let print_in_file () =
      Globals.set_entry_point funcname false;
      Kernel.Unicode.set false;
      let buf = Buffer.create 512 in
      let fmt = Format.formatter_of_buffer buf in
      File.pretty_ast ~fmt ();
      let out_file = open_out filename in
      Options.Self.feedback ~dkey:Options.dkey_mutant "mutant %i:" cpt;
      let dkeys = Options.Self.Debug_category.get() in
      if Datatype.String.Set.mem "mutant" dkeys then
	Buffer.output_buffer stdout buf;
      Buffer.output_buffer out_file buf;
      Format.pp_print_flush fmt ();
      flush stdout;
      flush out_file;
      close_out out_file;
      Buffer.clear buf
    in
    Project.on project print_in_file ();
    let ret = match Options.Apply_to_Mutant.get() with
      | "" -> false
      | plugins ->
	let cmd = Printf.sprintf "frama-c %s -main %s -no-unicode \
%s -then -werror -werror-no-unknown -werror-no-external"
	  filename funcname plugins in
	(Sys.command cmd) = 0
    in
    let k_m_cpt = if ret then killed_mutants_cpt else killed_mutants_cpt + 1 in
    Project.remove ~project ();
    mutate funcname (cpt+1) k_m_cpt ((cpt, ret, h) :: recap) t


let run() =
  if Options.Enabled.get() then
    let funcname = Kernel_function.get_name (fst (Globals.entry_point())) in
    let g = new gatherer funcname in
    Visitor.visitFramacFile (g :> Visitor.frama_c_inplace) (Ast.get());
    let mutations = g#get_mutations() in
    let n_mutations = List.length mutations in
    Options.Self.feedback ~dkey:Options.dkey_progress "%i mutants" n_mutations;
    let killed_mutants_cpt, recap = mutate funcname 0 0 [] mutations in
    let dkey = Options.dkey_report in
    Options.Self.result ~dkey "|      | Killed |   Not  |";
    List.iter (fun (i,r,m) ->
      Options.Self.result ~dkey "| %4i |   %c    |   %c    | %a"
	i (if r then ' ' else 'X') (if r then 'X' else ' ') pp_mutation m;
      Options.Self.result ~dkey "--------------------------"
    ) recap;
    Options.Self.result ~dkey "%i mutants" n_mutations;
    Options.Self.result ~dkey "%i mutants killed" killed_mutants_cpt
	
	
let run =
  let deps = [Ast.self; Options.Enabled.self] in
  let f, _self = State_builder.apply_once "MUT" deps run in
  f
    
let() = Db.Main.extend run
