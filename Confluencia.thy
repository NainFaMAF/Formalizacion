theory Confluencia
  imports Main Nominal2.Nominal2 LambdaCalculus
begin

\<comment> \<open>Notar que las relaciones de contraccion y reduccion paralela son 
 definidas mediante una funcion de tipo boolean\<close>
(* Propiedad Diamante para cualquier relación R : 
 \<forall> x,y,z . R(x,y) & R(x,z) \<Rightarrow> \<exists>c. R(y,c) & R(z,c) *)

definition is_church_rosser :: "(exp => exp => bool) => bool" where
  "is_church_rosser R \<equiv> \<forall>a b1 b2.
    Star R a b1 \<and> Star R a b2 \<longrightarrow> (\<exists>c. Star R b1 c \<and>  Star R b2 c)"

definition is_trans :: "('a => 'a => bool) => bool" where
 "is_trans R \<equiv> \<forall> x y z. R x y \<and> R y z \<longrightarrow> R x z"

definition is_reflex :: "('a => 'a => bool) => bool" where
 "is_reflex R \<equiv> \<forall> x. R x x"


(*... Hint Miguel : probar que si 
  (S \<subseteq> R \<and> R \<subseteq> S* \<and> is_church_rosser R) \<longrightarrow> is_church_rosser S  
donde  S es la relacion \<beta>-contraccion "Step" y R es la relacion de reduccion paralela "ParStep" ...*)

lemma Church_Rosser_Preservation:
  assumes "\<And>a b. S a b \<longrightarrow> R a b"
  assumes "\<And>a b. R a b \<longrightarrow> (Star S) a b"
  assumes "is_church_rosser R"
  shows "is_church_rosser (S)"
proof (unfold is_church_rosser_def, intro allI impI)
  fix a b1 b2
  assume "Star S a b1 \<and> Star S a b2"
  then have "Star S a b1" "Star S a b2" by simp_all
  then obtain c where "Star S b1 c" and "Star S b2 c" 
  proof (induction)
    case (refl a)
    then show ?case by (metis Star.refl)
  next
    case (step a b)
    assume "S a b"
    then obtain c where "Star S b c" and "Star S b2 c"
      sorry
    then show ?case sorry
  next
    case (trans a b c)
    then show ?case sorry
  qed
  then show " \<exists>c. Star S b1 c \<and> Star S b2 c" by auto
qed

lemma equivalencia :"StarOriginal R = Star R"  


(*Pasos del blueprint*)
(*Probar las 3 propiedades de la beta reduccion paralela :  *)
lemma prop1 : "(Step m n) \<longrightarrow> (ParStep m n)"
 sorry

lemma prop2 : "(ParStep m n) \<longrightarrow> (Star Step) m n"
 sorry

lemma prop3 : "(ParStep m n) \<and> (Parstep s t) \<longrightarrow> ParStep (subst_term m x s) (subst_term n x t)"
 sorry

(*Enunciado del Teorema de Confluencia de Church - Rosser*)
lemma Confluencia : "(Star Step) M N1 \<and> (Star Step) M N2 \<longrightarrow> (\<exists>C. (Star Step) N1 C \<and> (Star Step) N2 C)"
 sorry

end