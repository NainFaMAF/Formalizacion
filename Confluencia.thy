theory Confluencia
  imports Main Nominal2.Nominal2 LambdaCalculus
begin

\<comment> \<open>Notar que las relaciones de contraccion y reduccion paralela son 
 definidas mediante una funcion de tipo boolean\<close>
(* Propiedad Diamante para cualquier relación R : 
 \<forall> x,y,z . R(x,y) & R(x,z) \<Rightarrow> \<exists>c. R(y,c) & R(z,c) *)

definition is_church_rosser :: "('a => 'a => bool) => bool" where
  "is_church_rosser R \<equiv> \<forall>a b1 b2.
    R a b1 \<and> R a b2 \<longrightarrow> (\<exists>c. R b1 c \<and> R b2 c)"

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
  shows "is_church_rosser S"
proof (unfold is_church_rosser_def, intro allI impI)
  fix a b1 b2
  assume "S a b1" and "S a b2"
  obtain c where "R b1 c" and "R b2 c"
    by (metis \<open>S a b1\<close> \<open>S a b2\<close> assms(1) assms(3) is_church_rosser_def)
  have "R a b1" by (simp add: \<open>S a b1\<close> assms(1)) 
  moreover
  have "R a b2" by (simp add: \<open>S a b2\<close> assms(1))
  moreover
  have "Star S a b1" by (simp add: assms(2) calculation(1))
  moreover 
  have "Star S a b2" by (simp add: assms(2) calculation(2))
  moreover
  have "Star S b1 c" by (simp add: \<open>R b1 c\<close> assms(2))
  moreover 
  have "Star S b2 c" by (simp add: \<open>R b2 c\<close> assms(2))
  (* en este punto deberia poder probar "is_church_rosser (Star S)" *)
  (* esto serviria para probar \<open>S b1 c\<close> y \<open>S b2 c\<close> ? como ?  *)
    
   show ?thesis by (rule exI[where x=c]) (simp ad: \<open>S b1 c\<close> \<open>S b2 c\<close>)
  qed
qed

end