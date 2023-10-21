theory LambdaCalculus
  imports Main "Nominal2.Nominal2" "HOL-Eisbach.Eisbach"
begin

atom_decl var

nominal_datatype exp =
  Var var
  | App exp exp
  | Lam x::var body::exp binds x in body  ("Lam [_]. _" [100, 100] 100)

declare exp.fv_defs[simp]

(** subrules *)
nominal_function
  is_var :: "exp => bool"
  where
    "is_var (Var x) = (False)"
  | "is_var (App e1 e2) = (False)"
  | "is_var (Lam [x]. e) = ((True))"
          apply (all_trivials)
   apply (simp add: eqvt_def is_var_graph_aux_def)
  using exp.exhaust by blast
nominal_termination (eqvt)
  by lexicographic_order

method pat_comp_aux =
  (match premises in
    "x = (_ :: exp) \<Longrightarrow> _" for x \<Rightarrow> \<open>rule exp.strong_exhaust [where y = x and c = x]\<close>
    \<bar> "x = (Var _, _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule exp.strong_exhaust [where y = "fst x" and c = x]\<close>
    \<bar> "x = (_, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule exp.strong_exhaust [where y = "snd x" and c = x]\<close>
    \<bar> "x = (_, _, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule exp.strong_exhaust [where y = "snd (snd x)" and c = x]\<close>)

(** substitutions *)
nominal_function
  subst_term :: "exp => var => exp => exp" 
  where
    "subst_term (Var x) y e = ((if x=y then e else (Var x)))"
  | "atom x \<sharp> (y, e) \<Longrightarrow> subst_term (Lam [x]. b) y e = (Lam [x]. (subst_term b y e))"
  | "subst_term (App e1 e2) y e = (App (subst_term e1 y e) (subst_term e2 y e))"
          apply (all_trivials)
     apply (simp add: eqvt_def subst_term_graph_aux_def)
    apply(pat_comp_aux)
      apply(auto simp: fresh_star_def fresh_Pair)
   apply blast
  apply (auto simp: eqvt_at_def)
  apply (metis flip_fresh_fresh)+
  done
nominal_termination (eqvt) by lexicographic_order

lemma fresh_subst_term: "\<lbrakk> atom z \<sharp> s ; z = y \<or> atom z \<sharp> t \<rbrakk> \<Longrightarrow> atom z \<sharp> subst_term t y s"
  by (nominal_induct t avoiding: z y s rule: exp.strong_induct) auto

(** definitions *)
inductive Step :: "exp \<Rightarrow> exp \<Rightarrow> bool"
  and   "Step'" :: "exp \<Rightarrow> exp \<Rightarrow>  bool" ("_ \<mapsto> _" 100)
  where   "(e \<mapsto> e') \<equiv> Step (e) (e')"
  | ST_BetaI: "(App  (Lam [x]. e) e') \<mapsto>  (subst_term e x e')"
  | ST_AppL: "(e1 \<mapsto> e2) \<Longrightarrow> ((App e1 e) \<mapsto> (App e2 e))"
  | ST_AppR: "(e1 \<mapsto> e2) \<Longrightarrow> ((App e e1) \<mapsto> (App e e2))"
  | ST_Lam: " e1 \<mapsto> e2 \<Longrightarrow> (Lam [x]. e1) \<mapsto> (Lam [x]. e2)"
equivariance Step
nominal_inductive Step .

lemma id_red : "(App (Lam [x]. Var x) e) \<mapsto> e"
proof -
  have "App (Lam [x]. Var x) e \<mapsto> subst_term (Var x) x e"
    by (simp only:ST_BetaI)
    then
    show ?thesis by simp
qed
type_synonym rel = "exp \<Rightarrow> exp \<Rightarrow> bool"

inductive Star :: "rel \<Rightarrow> rel" for r where
   refl : "Star r a a"
 | step : "r a b ==> Star r a b"
 | trans : "Star r a b ==> Star r b c \<Longrightarrow> Star r a c"
equivariance Star

inductive ParStep :: "exp \<Rightarrow> exp \<Rightarrow> bool"
  and   "ParStep'" :: "exp \<Rightarrow> exp \<Rightarrow>  bool" ("_ \<rhd> _" 100)
  where   "(e \<rhd> e') \<equiv> ParStep (e) (e')"
  | ST_BetaI: "(App  (Lam [x]. e) e') \<rhd>  (subst_term e x e')"
  | ST_AppL: "(e1 \<rhd> e2) \<Longrightarrow> ((App e1 e) \<rhd> (App e2 e))"
  | ST_AppR: "(e1 \<rhd> e2) \<Longrightarrow> ((App e e1) \<rhd> (App e e2))"
  | ST_Lam: " e1 \<rhd> e2 \<Longrightarrow> (Lam [x]. e1) \<rhd> (Lam [x]. e2)"
equivariance ParStep
nominal_inductive ParStep .

end