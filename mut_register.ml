
open Cil_types


type mutation =
  (* mutations on code *)
  | Mut_BinOp of binop * binop * location
  | Mut_If of exp * exp * location
  (* mutations on spec *)
  | Mut_TBinOp of binop * binop * location
  | Mut_Prel of relation * relation * location
  | Mut_Pnot of predicate named * predicate named * location
  | Mut_LoopInv of predicate named
  | Mut_Post of identified_predicate
  | Mut_Term of term * term * location

let pp_aux fmt f e1 e2 loc =
  Format.fprintf fmt "%a: `%a` --> `%a`" Printer.pp_location loc f e1 f e2

let pp_mutation fmt = function
  | Mut_TBinOp(b1,b2,loc)
  | Mut_BinOp(b1,b2,loc) -> pp_aux fmt Printer.pp_binop b1 b2 loc
  | Mut_If(e1,e2,loc) -> pp_aux fmt Printer.pp_exp e1 e2 loc
  | Mut_Prel(r1,r2,loc) -> pp_aux fmt Printer.pp_relation r1 r2 loc
  | Mut_Pnot(p1,p2,loc) -> pp_aux fmt Printer.pp_predicate_named p1 p2 loc
  | Mut_LoopInv p -> Format.fprintf fmt "%a: - loop invariant %a"
    Printer.pp_location p.loc Printer.pp_predicate_named p
  | Mut_Post p -> Format.fprintf fmt "%a: - ensures %a"
    Printer.pp_location p.ip_loc Printer.pp_identified_predicate p
  | Mut_Term(t1,t2,loc) -> pp_aux fmt Printer.pp_term t1 t2 loc


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
  val mutable postcond_or_invariant = false

  method get_mutations() = mutations
  method private add m = mutations <- m :: mutations

  method! vbehavior bhv =
    let kf = Extlib.the (self#current_kf) in
    let add (_,p) = self#add (Mut_Post p) in
    if Kernel_function.get_name kf <> funcname then
      match bhv.b_post_cond with
      | (_,h)::_ as l when Mut_options.Mut_Spec.get() && loc_ok h.ip_loc ->
	 postcond_or_invariant <- true;
	 List.iter add l;
	 Cil.DoChildrenPost (fun x -> postcond_or_invariant <- false; x)
      | _ -> Cil.DoChildren
    else (* for main function: only mutate postcondition predicates *)
      let f (_,h) = ignore (self#videntified_predicate h) in
      List.iter f bhv.b_post_cond;
      Cil.SkipChildren

  method! vcode_annot ca = match ca.annot_content with
  | AInvariant(_,b,p) when Mut_options.Mut_Spec.get() && b && loc_ok p.loc ->
     postcond_or_invariant <- true;
     self#add (Mut_LoopInv p);
     Cil.DoChildrenPost (fun x -> postcond_or_invariant <- false; x)
  | _ -> Cil.DoChildren

  method! vpredicate_named p = match p.content with
  | Pexists(_,{content=Pand(_,y)})
  | Pforall(_,{content=Pimplies(_,y)}) ->
    ignore (self#vpredicate_named y);
    Cil.SkipChildren
  | Prel(r,t1,t2) when Mut_options.Mut_Spec.get() && loc_ok p.loc ->
    let add o = self#add (Mut_Prel (r, o, p.loc)) in
    List.iter add (other_relations r);
    begin
      if postcond_or_invariant then
	let l = [1;2;3] in
	match r with
	| Rle
	| Rlt ->
	   List.iter (fun i -> self#add (Mut_Term(t2,(add_i i t2),p.loc))) l
	| Rge
	| Rgt ->
	   List.iter (fun i -> self#add (Mut_Term(t1,(add_i i t1),p.loc))) l
	| _ -> ()
    end;
    Cil.DoChildren
  | Pnot(p2) when Mut_options.Mut_Spec.get() && loc_ok p.loc ->
    self#add (Mut_Pnot (p, p2, p.loc));
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
    | GVarDecl (_,_,l) when loc_ok l -> Cil.DoChildren
    | GVarDecl _ -> Cil.SkipChildren
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
  | AInvariant(_,linv,p), Mut_LoopInv m when linv && same_locs p.loc m.loc ->
    let ca2 = AInvariant([],true,Logic_const.ptrue) in
    Cil.ChangeDoChildrenPost (ca, fun _ -> Logic_const.new_code_annotation ca2)
  | _ -> Cil.DoChildren

  method! vpredicate_named p = match p.content, mut with
  | Prel(r,x,y), Mut_Prel(w,z,l) when same_locs p.loc l && r = w ->
    Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (z,x,y))
  | Prel(r,x,y), Mut_Term(a,b,l)
       when same_locs p.loc l && x.term_loc = a.term_loc ->
     Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (r,b,y))
  | Prel(r,x,y), Mut_Term(a,b,l)
       when same_locs p.loc l && y.term_loc = a.term_loc ->
     Cil.ChangeDoChildrenPost (p, fun _ -> Logic_const.prel (r,x,b))
  | Pnot(_), Mut_Pnot(_,y,l) when same_locs p.loc l ->
    Cil.ChangeDoChildrenPost (p, fun _ -> y)
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

type verdict = Not_tried | Verdict of bool * CalendarLib.Ftime.Period.t

let pp_verdict fmt = function
  | Not_tried -> Format.fprintf fmt "-"
  | Verdict (true,_) -> Format.fprintf fmt "T"
  | Verdict (false,_) -> Format.fprintf fmt "F"

type mutant = {
  id : int;
  mutation : mutation;
  is_proved : verdict;
  nc_detected : verdict;
  cw_detected : verdict;
  stady_time : CalendarLib.Ftime.Period.t option;
}

let pp_time fmt t =
  let length = CalendarLib.Ftime.Period.length t in
  Format.fprintf fmt "%f" length

let pp_mutant fmt m =
  Format.fprintf fmt "| %4i |    %a   |  %a  |  %a  | %a"
		 m.id
		 pp_verdict m.is_proved
		 pp_verdict m.nc_detected
		 pp_verdict m.cw_detected
		 pp_mutation m.mutation

let wp_timeout = 40
let stady_timeout = 5
let pattern = "\\[wp\\] Proved goals:[ ]*\\([0-9]*\\)[ ]*\\/[ ]*\\([0-9]*\\)"
let sed_cmd = Printf.sprintf "sed 's/%s/[ \\1 -eq \\2 ]/'" pattern

let rec mutate fct cpt recap = function
  | [] -> recap
  | _ when Mut_options.Only.get() <> -1 && Mut_options.Only.get() < cpt -> recap
  | _::t when Mut_options.Only.get() <> -1 && Mut_options.Only.get() > cpt ->
    mutate fct (cpt+1) recap t
  | h::t ->
    let file = "mutant_" ^ (string_of_int cpt) ^ ".c" in
    let dkey = Mut_options.dkey_progress in
    Mut_options.Self.feedback ~dkey "mutant %i %a" cpt pp_mutation h;
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
    let log_file = "__mut.log" in
    let mutant =
      {id=cpt; mutation=h; is_proved=Not_tried; nc_detected=Not_tried;
       cw_detected=Not_tried; stady_time=None;} in
    let cmd =
      Printf.sprintf
	"frama-c %s -wp -wp-out . -wp-timeout %i -wp-prover alt-ergo,cvc3 | \
	 tee -a %s | grep Proved | $(%s)"
	file wp_timeout log_file sed_cmd in
    let begin_wp_time = CalendarLib.Ftime.now() in
    let is_proved = (Sys.command cmd) = 0 in
    let end_wp_time = CalendarLib.Ftime.now() in
    let diff_wp_time = CalendarLib.Ftime.sub end_wp_time begin_wp_time in
    let mutant = { mutant with is_proved = Verdict (is_proved, diff_wp_time)} in
    let mutant =
      if is_proved then mutant
      else
	begin
	  Mut_options.Self.feedback ~dkey "not proved";
	  let cmd =
	    Printf.sprintf
	      "frama-c %s -main %s -rte -then -stady \
	       -stady-stop-when-assert-violated -stady-timeout %i \
	       -stady-pc-options=\"-pc-k-path=4\" | tee -a %s | \
	       grep DRIVER:"
	      file fct stady_timeout log_file in
	  let begin_ncd_time = CalendarLib.Ftime.now() in
	  let nc_detected = (Sys.command cmd) = 0 in
	  let end_ncd_time = CalendarLib.Ftime.now() in
	  let diff_ncd_time =
	    CalendarLib.Ftime.sub end_ncd_time begin_ncd_time in
	  let mutant =
	    { mutant with nc_detected = Verdict (nc_detected, diff_ncd_time)} in
	  let mutant = { mutant with stady_time = Some diff_ncd_time } in
	  if nc_detected then mutant
	  else
	    begin
	      Mut_options.Self.feedback ~dkey "no NC detected";
	      let on_int already_detected i =
		let cmd =
		  Printf.sprintf
		    "frama-c %s -main %s -rte -then \
		     -stady -stady-stop-when-assert-violated \
		     -stady-timeout %i -stady-swd %i \
		     -stady-pc-options=\"-pc-k-path=4\" | \
		     tee -a %s | grep DRIVER:"
		    file fct stady_timeout i log_file in
		already_detected || (Sys.command cmd) = 0
	      in
	      let l = Mut_options.Contract_weakness_detection.get() in
	      let l = List.map int_of_string l in
	      let begin_cwd_time = CalendarLib.Ftime.now() in
	      let cw_detected =	List.fold_left on_int false l in
	      let end_cwd_time = CalendarLib.Ftime.now() in
	      let diff_cwd_time =
		CalendarLib.Ftime.sub end_cwd_time begin_cwd_time in
	      let diff_stady_time =
		CalendarLib.Ftime.sub end_cwd_time begin_ncd_time in
	      let mutant = {mutant with stady_time = Some diff_stady_time } in
	      { mutant with cw_detected = Verdict (cw_detected, diff_cwd_time) }
	    end
	end
    in
    Mut_options.Self.feedback ~dkey "%a" pp_mutant mutant;
    mutate fct (cpt+1) (mutant :: recap) t


let data_of o l ok_max_t ok_sum_t ok_nb_t ko_max_t ko_sum_t ko_nb_t = function
  | Not_tried -> (l, ok_max_t, ok_sum_t, ok_nb_t, ko_max_t, ko_sum_t, ko_nb_t)
  | Verdict (true, t) ->
     o::l,
     (if CalendarLib.Ftime.Period.length t < ok_max_t then
	ok_max_t else CalendarLib.Ftime.Period.length t),
     ok_sum_t +. CalendarLib.Ftime.Period.length t,
     ok_nb_t + 1, ko_max_t, ko_sum_t, ko_nb_t
  | Verdict (false, t) ->
     l, ok_max_t, ok_sum_t, ok_nb_t,
     (if CalendarLib.Ftime.Period.length t < ko_max_t then
	ko_max_t else CalendarLib.Ftime.Period.length t),
     ko_sum_t +. CalendarLib.Ftime.Period.length t, ko_nb_t + 1


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
    let recap = mutate funcname 0 [] mutations in
    let dkey = Mut_options.dkey_report in
    let pp fmt x =
      let pp_aux fmt x = Format.fprintf fmt "%i" x.id in
      Format.fprintf fmt "(%a)" (Pretty_utils.pp_list ~sep:"," pp_aux) x
    in
    (* WP on initial program *)
    let cmd =
      Printf.sprintf
	"frama-c %s -wp -wp-out . -wp-timeout %i -wp-prover alt-ergo,cvc3 | \
	 grep Proved | $(%s)"
	filename wp_timeout sed_cmd in
    let begin_time = CalendarLib.Ftime.now() in
    assert((Sys.command cmd) = 0);
    let end_time = CalendarLib.Ftime.now() in
    let diff_time = CalendarLib.Ftime.sub end_time begin_time in
    let diff_t = CalendarLib.Ftime.Period.length diff_time in
    (* Report *)
    Mut_options.Self.result ~dkey "|      | Proved | NCD | CWD |";
    let on_mutant
	  (wp, wp_ok_max_t, wp_ok_sum_t, wp_ok_nb_t,
	   wp_ko_max_t, wp_ko_sum_t, wp_ko_nb_t,
	   ncd, ncd_ok_max_t, ncd_ok_sum_t, ncd_ok_nb_t,
	   ncd_ko_max_t, ncd_ko_sum_t, ncd_ko_nb_t,
	   cwd, cwd_ok_max_t, cwd_ok_sum_t, cwd_ok_nb_t,
	   cwd_ko_max_t, cwd_ko_sum_t, cwd_ko_nb_t,
	   sd_max_t, sd_sum_t, sd_nb_t) m =
      let wp, wp_ok_max_t, wp_ok_sum_t, wp_ok_nb_t,
	  wp_ko_max_t, wp_ko_sum_t, wp_ko_nb_t =
	data_of m wp wp_ok_max_t wp_ok_sum_t wp_ok_nb_t
		wp_ko_max_t wp_ko_sum_t wp_ko_nb_t m.is_proved in
      let ncd, ncd_ok_max_t, ncd_ok_sum_t, ncd_ok_nb_t,
	  ncd_ko_max_t, ncd_ko_sum_t, ncd_ko_nb_t =
	data_of m ncd ncd_ok_max_t ncd_ok_sum_t ncd_ok_nb_t
		ncd_ko_max_t ncd_ko_sum_t ncd_ko_nb_t m.nc_detected in
      let cwd, cwd_ok_max_t, cwd_ok_sum_t, cwd_ok_nb_t,
	  cwd_ko_max_t, cwd_ko_sum_t, cwd_ko_nb_t =
	data_of m cwd cwd_ok_max_t cwd_ok_sum_t cwd_ok_nb_t
		cwd_ko_max_t cwd_ko_sum_t cwd_ko_nb_t m.cw_detected in
      let sd_max_t, sd_sum_t, sd_nb_t =
	match m.stady_time with
	| None -> sd_max_t, sd_sum_t, sd_nb_t
	| Some t ->
	   (if CalendarLib.Ftime.Period.length t < sd_max_t then
	      sd_max_t else CalendarLib.Ftime.Period.length t),
	   sd_sum_t +. CalendarLib.Ftime.Period.length t,
	   sd_nb_t+1
      in
      Mut_options.Self.result ~dkey "%a" pp_mutant m;
      Mut_options.Self.result ~dkey "--------------------------";
      wp, wp_ok_max_t, wp_ok_sum_t, wp_ok_nb_t,
      wp_ko_max_t, wp_ko_sum_t, wp_ko_nb_t,
      ncd, ncd_ok_max_t, ncd_ok_sum_t, ncd_ok_nb_t,
      ncd_ko_max_t, ncd_ko_sum_t, ncd_ko_nb_t,
      cwd, cwd_ok_max_t, cwd_ok_sum_t, cwd_ok_nb_t,
      cwd_ko_max_t, cwd_ko_sum_t, cwd_ko_nb_t,
      sd_max_t, sd_sum_t, sd_nb_t
    in
    let wp, wp_ok_max_t, wp_ok_sum_t, wp_ok_nb_t,
      wp_ko_max_t, wp_ko_sum_t, wp_ko_nb_t,
      ncd, ncd_ok_max_t, ncd_ok_sum_t, ncd_ok_nb_t,
      ncd_ko_max_t, ncd_ko_sum_t, ncd_ko_nb_t,
      cwd, cwd_ok_max_t, cwd_ok_sum_t, cwd_ok_nb_t,
      cwd_ko_max_t, cwd_ko_sum_t, cwd_ko_nb_t,
      sd_max_t, sd_sum_t, sd_nb_t =
      (* neutral element of max is NaN *)
      List.fold_left on_mutant
		     ([],diff_t,diff_t,1,nan,0.,0,
		      [],nan,0.,0,nan,0.,0,
		      [],nan,0.,0,nan,0.,0,
		      nan,0.,0)
		     recap in
    let wp_ok_mean_t = wp_ok_sum_t /. (float_of_int wp_ok_nb_t) in
    let wp_ko_mean_t = wp_ko_sum_t /. (float_of_int wp_ko_nb_t) in
    let ncd_ok_mean_t = ncd_ok_sum_t /. (float_of_int ncd_ok_nb_t) in
    let ncd_ko_mean_t = ncd_ko_sum_t /. (float_of_int ncd_ko_nb_t) in
    let cwd_ok_mean_t = cwd_ok_sum_t /. (float_of_int cwd_ok_nb_t) in
    let cwd_ko_mean_t = cwd_ko_sum_t /. (float_of_int cwd_ko_nb_t) in
    let sd_mean_t = sd_sum_t /. (float_of_int sd_nb_t) in
    let ncd_efficiency =
      (float_of_int ((List.length ncd) * 100)) /.
	(float_of_int ((n_mutations - (List.length wp)))) in
    let cwd_efficiency =
      (float_of_int ((List.length cwd) * 100)) /.
	(float_of_int ((n_mutations - (List.length wp) - (List.length ncd)))) in
    let ncd_cwd_efficiency =
      (float_of_int (((List.length ncd) + (List.length cwd)) * 100)) /.
	(float_of_int ((n_mutations - (List.length wp))))
    in
    let is_unknown m = match m.is_proved, m.nc_detected, m.cw_detected with
      | Verdict(false,_), Verdict(false,_), Verdict(false,_) -> true
      | _ -> false
    in
    let idk = List.filter is_unknown recap in
    Mut_options.Self.result ~dkey "%i mutants" n_mutations;
    Mut_options.Self.result ~dkey "%i proved %a" (List.length wp) pp wp;
    Mut_options.Self.result ~dkey "%i NC detected %a" (List.length ncd) pp ncd;
    Mut_options.Self.result ~dkey "%i CW detected %a" (List.length cwd) pp cwd;
    Mut_options.Self.result ~dkey "%i unknown %a" (List.length idk) pp idk;
    Mut_options.Self.result ~dkey "NCD efficiency %f%%" ncd_efficiency;
    Mut_options.Self.result ~dkey "CWD efficiency %f%%" cwd_efficiency;
    Mut_options.Self.result ~dkey "NCD+CWD efficiency %f%%" ncd_cwd_efficiency;
    (* LaTeX output *)
    let tex_file = "__mut.tex" in
    let out_file = open_out tex_file in
    Printf.fprintf out_file
		   "%s & %i & \
		    %i & %f & %f & %f & %f & \
		    %i & %f & %f & %f & %f & \
		    %f & \
		    %i & %f & %f & %f & %f & \
		    %f & \
		    %f & %f \
		    %f & \
		    %i \\\\ \n"
		   funcname n_mutations
		   (List.length wp)
		   wp_ok_max_t wp_ok_mean_t wp_ko_max_t wp_ko_mean_t
		   (List.length ncd)
		   ncd_ok_max_t ncd_ok_mean_t ncd_ko_max_t ncd_ko_mean_t
		   ncd_efficiency
		   (List.length cwd)
		   cwd_ok_max_t cwd_ok_mean_t cwd_ko_max_t cwd_ko_mean_t
		   cwd_efficiency
		   sd_max_t sd_mean_t
		   ncd_cwd_efficiency
		   (List.length idk);
    flush out_file;
    close_out out_file;
    (* .dat output *)
    let dat_file = "__mut.dat" in
    let out_file = open_out dat_file in
    Printf.fprintf out_file
		   "%s  %i  \
		    %i  %f  %f  %f  %f  \
		    %i  %f  %f  %f  %f  \
		    %f  \
		    %i  %f  %f  %f  %f  \
		    %f  \
		    %f  %f  \
		    %f  \
		    %i  \n"
		   funcname n_mutations
		   (List.length wp)
		   wp_ok_max_t wp_ok_mean_t wp_ko_max_t wp_ko_mean_t
		   (List.length ncd)
		   ncd_ok_max_t ncd_ok_mean_t ncd_ko_max_t ncd_ko_mean_t
		   ncd_efficiency
		   (List.length cwd)
		   cwd_ok_max_t cwd_ok_mean_t cwd_ko_max_t cwd_ko_mean_t
		   cwd_efficiency
		   sd_max_t sd_mean_t
		   ncd_cwd_efficiency
		   (List.length idk);
    flush out_file;
    close_out out_file

	
let run =
  let deps = [Ast.self; Mut_options.Enabled.self] in
  let f, _self = State_builder.apply_once "mutation" deps run in
  f
    
let() = Db.Main.extend run
