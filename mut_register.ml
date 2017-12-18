
open Cil_types


type mutation =
  (* mutations on code *)
  | Mut_BinOp of binop * binop * location
  | Mut_If of exp * exp * location
  (* mutations on spec *)
  | Mut_TBinOp of binop * binop * location
  | Mut_Prel of relation * relation * location
  | Mut_Pnot of predicate * predicate * location
  | Mut_LoopInv of predicate
  | Mut_Post of identified_predicate
  | Mut_Term of term * term * location
  | Mut_Variant of term * term * location
  | Mut_And of predicate * bool * location

let pp_aux fmt f e1 e2 loc =
  Format.fprintf fmt "%a: `%a` --> `%a`" Printer.pp_location loc f e1 f e2

let pp_mutation fmt = function
  | Mut_TBinOp(b1,b2,loc)
  | Mut_BinOp(b1,b2,loc) -> pp_aux fmt Printer.pp_binop b1 b2 loc
  | Mut_If(e1,e2,loc) -> pp_aux fmt Printer.pp_exp e1 e2 loc
  | Mut_Prel(r1,r2,loc) -> pp_aux fmt Printer.pp_relation r1 r2 loc
  | Mut_Pnot(p1,p2,loc) -> pp_aux fmt Printer.pp_predicate p1 p2 loc
  | Mut_LoopInv p -> Format.fprintf fmt "%a: - loop invariant %a"
    Printer.pp_location p.pred_loc Printer.pp_predicate p
  | Mut_Post p -> Format.fprintf fmt "%a: - ensures %a"
    Printer.pp_location p.ip_content.pred_loc Printer.pp_identified_predicate p
  | Mut_Term(t1,t2,loc) -> pp_aux fmt Printer.pp_term t1 t2 loc
  | Mut_Variant(t1,t2,loc) -> pp_aux fmt Printer.pp_term t1 t2 loc
  | Mut_And (p,b,loc) ->
     let side = if b then "left" else "right" in
     Format.fprintf fmt "%a: %a cut %s"
       Printer.pp_location loc Printer.pp_predicate p side


let other_binops = function
  | PlusA -> [MinusA;Mult]
  | MinusA -> [PlusA;Mult]
  | Mult -> [PlusA;MinusA]
  | Div -> [Mult;PlusA;MinusA;Mod]
  | Mod -> [Mult;Div;PlusA;MinusA]
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

let add_i i t =
  Logic_const.term (TBinOp(PlusA,t,Logic_const.tinteger i)) t.term_type

class gatherer funcname = object(self)
  inherit Visitor.frama_c_inplace

  val mutable mutations = []
  val mutable in_postcond = false
  val mutable in_invariant = false
  val mutable in_quantif = false

  method get_mutations() = mutations
  method private add m = mutations <- m :: mutations

  method! vbehavior bhv =
    let kf = Extlib.the (self#current_kf) in
    let add (_,p) = self#add (Mut_Post p) in
    if Kernel_function.get_name kf <> funcname then
      match bhv.b_post_cond with
      | (_,h)::_ as l
	  when Mut_options.Mut_Spec.get() && loc_ok h.ip_content.pred_loc ->
	 in_postcond <- true;
	 List.iter add l;
	 Cil.DoChildrenPost (fun x -> in_postcond <- false; x)
      | _ -> Cil.DoChildren
    else (* for main function: only mutate postcondition predicates *)
      let f (_,h) = ignore (self#videntified_predicate h) in
      List.iter f bhv.b_post_cond;
      Cil.SkipChildren

  method! vcode_annot ca = match ca.annot_content with
  | AInvariant(_,b,p)
      when Mut_options.Mut_Spec.get() && b && loc_ok p.pred_loc ->
     in_invariant <- true;
     self#add (Mut_LoopInv p);
     Cil.DoChildrenPost (fun x -> in_invariant <- false; x)
  | AVariant(t,_) ->
     let neg t = Logic_const.term (TUnOp(Neg,t)) t.term_type in
     let add t x = Logic_const.term (TBinOp(PlusA,t,x)) t.term_type in
     let sub t x = Logic_const.term (TBinOp(MinusA,t,x)) t.term_type in
     (* v -> v +/- 1, 5, 10 *)
     self#add (Mut_Variant(t, add t (Logic_const.tinteger 1), t.term_loc));
     self#add (Mut_Variant(t, sub t (Logic_const.tinteger 1), t.term_loc));
     self#add (Mut_Variant(t, add t (Logic_const.tinteger 5), t.term_loc));
     self#add (Mut_Variant(t, sub t (Logic_const.tinteger 5), t.term_loc));
     self#add (Mut_Variant(t, add t (Logic_const.tinteger 10), t.term_loc));
     self#add (Mut_Variant(t, sub t (Logic_const.tinteger 10), t.term_loc));
     (* v -> -v *)
     self#add (Mut_Variant(t, neg t, t.term_loc));
     (* v -> - v +/- 1, 5, 10 *)
     self#add (Mut_Variant(t, neg(add t(Logic_const.tinteger 1)), t.term_loc));
     self#add (Mut_Variant(t, neg(sub t(Logic_const.tinteger 1)), t.term_loc));
     self#add (Mut_Variant(t, neg(add t(Logic_const.tinteger 5)), t.term_loc));
     self#add (Mut_Variant(t, neg(sub t(Logic_const.tinteger 5)), t.term_loc));
     self#add (Mut_Variant(t, neg(add t(Logic_const.tinteger 10)), t.term_loc));
     self#add (Mut_Variant(t, neg(sub t(Logic_const.tinteger 10)), t.term_loc));
     Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vpredicate p = match p.pred_content with
  | Pexists(_,{pred_content=Pand(_,y)})
  | Pforall(_,{pred_content=Pimplies(_,y)}) ->
     in_quantif <- true;
     ignore (self#vpredicate y);
     in_quantif <- false;
     Cil.SkipChildren
  | Prel(r,t1,t2) when Mut_options.Mut_Spec.get() && loc_ok p.pred_loc ->
    let add o = self#add (Mut_Prel (r, o, p.pred_loc)) in
    List.iter add (other_relations r);
    begin
      if (in_postcond || in_invariant) && not in_quantif then
	let l = [1;2;3] in
	match r with
	| Rle
	| Rlt ->
	   List.iter(fun i -> self#add (Mut_Term(t2,(add_i i t2),p.pred_loc))) l
	| Rge
	| Rgt ->
	   List.iter(fun i -> self#add (Mut_Term(t1,(add_i i t1),p.pred_loc))) l
	| _ -> ()
    end;
    Cil.DoChildren
  | Pnot(p2) when Mut_options.Mut_Spec.get() && loc_ok p.pred_loc ->
    self#add (Mut_Pnot (p, p2, p.pred_loc));
    Cil.DoChildren
  | Pand _ when Mut_options.Mut_Spec.get() && loc_ok p.pred_loc ->
     if in_invariant && not in_quantif then
       begin
	 self#add (Mut_And (p, true, p.pred_loc));
	 self#add (Mut_And (p, false, p.pred_loc))
       end;
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vterm t = match t.term_node with
  | TBinOp((PlusA|MinusA|Mult|Div|Mod|LAnd|LOr|Lt|Gt|Le|Ge|Eq|Ne) as op, _, _)
       when Mut_options.Mut_Spec.get() && loc_ok t.term_loc ->
     let add o = self#add (Mut_TBinOp (op, o, t.term_loc)) in
     List.iter add (other_binops op);
     Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vexpr exp = match exp.enode with
  | BinOp((PlusA|MinusA|Mult|Div|Mod|LAnd|LOr|Lt|Gt|Le|Ge|Eq|Ne) as op, _, _, _)
       when Mut_options.Mut_Code.get() ->
     let add o = self#add (Mut_BinOp (op, o, exp.eloc)) in
     List.iter add (other_binops op);
     Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vstmt_aux stmt = match stmt.skind with
  | If (exp, _, _, loc) when Mut_options.Mut_Code.get() ->
    let new_bool = Cil.new_exp loc (UnOp (LNot, exp, Cil.intType)) in
    self#add (Mut_If(exp, new_bool, loc));
    Cil.DoChildren
  | _ -> Cil.DoChildren

  method! vglob_aux glob =
    match glob with
    | GType (_,l) when loc_ok l -> Cil.DoChildren
    | GType _ -> Cil.SkipChildren
    | GCompTag (_,l) when loc_ok l -> Cil.DoChildren
    | GCompTag _ -> Cil.SkipChildren
    | GCompTagDecl (_,l) when loc_ok l -> Cil.DoChildren
    | GCompTagDecl _ -> Cil.SkipChildren
    | GEnumTag (_,l) when loc_ok l -> Cil.DoChildren
    | GEnumTag _ -> Cil.SkipChildren
    | GEnumTagDecl (_,l) when loc_ok l -> Cil.DoChildren
    | GEnumTagDecl _ -> Cil.SkipChildren
    | GVarDecl (_,l) when loc_ok l -> Cil.DoChildren
    | GVarDecl _ -> Cil.SkipChildren
    | GFunDecl (_,_,l) when loc_ok l -> Cil.DoChildren
    | GFunDecl _ -> Cil.SkipChildren
    | GVar (_,_,l) when loc_ok l -> Cil.DoChildren
    | GVar _ -> Cil.SkipChildren
    | GFun (f,_) when f.svar.vname = (funcname ^ "_precond") -> Cil.SkipChildren
    | GFun (_,l) when loc_ok l -> Cil.DoChildren
    | GFun _ -> Cil.SkipChildren
    | GAsm _ -> Cil.SkipChildren
    | GPragma _ -> Cil.SkipChildren
    | GText _ -> Cil.SkipChildren
    | GAnnot _ -> Cil.SkipChildren

  method! vassigns _ = Cil.SkipChildren
end


let same_locs l1 l2 = (Cil_datatype.Location.compare l1 l2) = 0


class mutation_visitor prj mut = object
  inherit Visitor.frama_c_copy prj

  method! vbehavior bhv = match mut with
  | Mut_Post m ->
    let l = List.filter (fun (_,p) -> p.ip_id <> m.ip_id) bhv.b_post_cond in
    (*Cil.ChangeDoChildrenPost (bhv, fun b -> {b with b_post_cond = l})*)
    Cil.ChangeTo {bhv with b_post_cond = l}
  | _ -> Cil.DoChildren

  method! vcode_annot ca = match ca.annot_content, mut with
  | AInvariant(_,linv,p), Mut_LoopInv m
    when linv && same_locs p.pred_loc m.pred_loc ->
     let ca2 = AInvariant([],true,Logic_const.ptrue) in
     Cil.ChangeDoChildrenPost (ca, fun _ -> Logic_const.new_code_annotation ca2)
  | AVariant (t, str), Mut_Variant (_t1,t2,l) when same_locs t.term_loc l ->
     let ca2 = AVariant (t2, str) in
     Cil.ChangeDoChildrenPost (ca, fun _ -> Logic_const.new_code_annotation ca2)
  | _ -> Cil.DoChildren

  method! vpredicate p = match p.pred_content, mut with
  | Prel(r,x,y), Mut_Prel(w,z,l) when same_locs p.pred_loc l && r = w ->
    Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (z,x,y))
  | Prel(r,x,y), Mut_Term(a,b,l)
       when same_locs p.pred_loc l && x.term_loc = a.term_loc ->
     Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (r,b,y))
  | Prel(r,x,y), Mut_Term(a,b,l)
       when same_locs p.pred_loc l && y.term_loc = a.term_loc ->
     Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (r,x,b))
  | Pnot(_), Mut_Pnot(_,y,l) when same_locs p.pred_loc l ->
    Cil.ChangeDoChildrenPost (p, fun _ -> y)
  | Pand(p1,p2), Mut_And(_,side,l) when same_locs p.pred_loc l ->
    Cil.ChangeDoChildrenPost (p, fun _ -> if side then p2 else p1)
  | _ -> Cil.DoChildren

  method! vterm term = match term.term_node, mut with
  | TBinOp(o,x,y), Mut_TBinOp(w,z,l) when same_locs term.term_loc l && o = w ->
    Cil.ChangeDoChildrenPost
      (term, fun t -> Logic_const.term (TBinOp(z,x,y)) t.term_type)
  | _ -> Cil.DoChildren

  method! vexpr exp = match exp.enode, mut with
  | BinOp (o1,x,y,t), Mut_BinOp (o2,z,l) when same_locs exp.eloc l && o1 = o2 ->
    Cil.ChangeDoChildrenPost (exp, fun e -> Cil.new_exp e.eloc (BinOp(z,x,y,t)))
  | _ -> Cil.DoChildren

  method! vstmt_aux stmt = match stmt.skind, mut with
  | If (e, x, y, loc), Mut_If (_, _, l) when same_locs loc l ->
    let e = Cil.new_exp loc (UnOp (LNot, e, Cil.intType)) in
    Cil.ChangeDoChildrenPost (stmt, fun s -> {s with skind = If (e, x, y, loc)})
  | _ -> Cil.DoChildren
end


let rec mutate fct cpt = function
  | [] -> ()
  | _ when Mut_options.Only.get() <> -1 && Mut_options.Only.get() < cpt -> ()
  | _::t when Mut_options.Only.get() <> -1 && Mut_options.Only.get() > cpt ->
    mutate fct (cpt+1) t
  | h::t ->
    let file = "mutant_" ^ (string_of_int cpt) ^ ".c" in
    (*
    let dkey = Mut_options.dkey_progress in
    if not (Mut_options.Generate_Only.get()) then
      Mut_options.Self.feedback ~dkey "mutant %i %a" cpt pp_mutation h;
    *)
    let f p = new mutation_visitor p h in
    let project = File.create_project_from_visitor "__mut_tmp" f in
    Project.copy ~selection:(Parameter_state.get_selection()) project;
    let print_in_file () =
      Globals.set_entry_point fct false;
      Kernel.Unicode.set false;
      let buf = Buffer.create 512 in
      let fmt = Format.formatter_of_buffer buf in
      File.pretty_ast ~fmt ();
      let out_file = open_out file in
      Mut_options.Self.feedback ~dkey:Mut_options.dkey_mutant "mutant %i:" cpt;
      let dkeys = Mut_options.Self.Debug_category.get() in
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
    Project.remove ~project ();
    mutate fct (cpt+1) t



let run() =
  if Mut_options.Enabled.get() then
    let filename = List.hd(Kernel.Files.get()) in
    let funcname = Kernel_function.get_name (fst (Globals.entry_point())) in
    let g = new gatherer funcname in
    Visitor.visitFramacFile (g :> Visitor.frama_c_inplace) (Ast.get());
    let mutations = g#get_mutations() in
    let n_mutations = List.length mutations in
    let dkey = Mut_options.dkey_progress in
    Mut_options.Self.feedback ~dkey "%i mutants" n_mutations;
    mutate funcname 0 mutations
    

	
let run =
  let deps = [Ast.self; Mut_options.Enabled.self] in
  let f, _self = State_builder.apply_once "mutation" deps run in
  f
    
let() = Db.Main.extend run
