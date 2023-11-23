theory Confluencia
  imports Main Nominal2.Nominal2 LambdaCalculus
begin

\<comment> \<open>Notar que las relaciones de contraccion y reduccion paralela son 
 definidas mediante una funcion de tipo boolean\<close>
(* Propiedad Diamante para cualquier relación R : 
 \<forall> x,y,z . R(x,y) & R(x,z) \<Rightarrow> \<exists>c. R(y,c) & R(z,c) *)

definition is_church_rosser :: "(exp => exp => bool) => bool" where
 "is_church_rosser R \<equiv> \<forall>a b1 b2.
    (Star R a b1 \<and> Star R a b2) \<longrightarrow> (\<exists>c. Star R b1 c \<and>  Star R b2 c)"

definition is_trans :: "('a => 'a => bool) => bool" where
 "is_trans R \<equiv> \<forall> x y z. (R x y \<and> R y z) \<longrightarrow> R x z"

definition is_reflex :: "('a => 'a => bool) => bool" where
 "is_reflex R \<equiv> \<forall> x. R x x"

definition is_simetric :: "('a => 'a => bool) => bool" where
 "is_simetric R \<equiv> \<forall> x y. R x y \<longrightarrow> R y x"

definition have_diamond_prop :: "('a => 'a => bool) => bool" where
 "have_diamond_prop R \<equiv> \<forall>x y z.( R x y \<and> R x z) \<longrightarrow> (\<exists>c. R y c \<and> R z c)"


lemma equiv_Stars : "StarOriginal R \<equiv> Star R" 
 sorry

(*un lema de ensayo*)
lemma 0:
  assumes "have_diamond_prop S"
  assumes "S a b"
  assumes "S a c"
  shows "\<exists>d.( S b d \<and> S c d)"
proof -
  have "S a b" using assms(2) by (simp add: assms(2))
  have "S a c" using assms(3) by (simp add: assms(3))
  then have "\<exists>d. S b d \<and> S c d" using assms(1) assms(2) assms(3) by (simp add: have_diamond_prop_def)
  then show ?thesis by auto
qed

(* Lema 1 del pdf  "Terms" *)
lemma uno:
  assumes h1: "\<And>a b c. (S a b \<and> Star S a c) " 
  assumes h2: "have_diamond_prop S"
  (*assumes h3:"\<And>x y. (S x y \<longrightarrow> Star S x y) " *)
  (*assumes h4: "is_reflex S" *)
  shows "\<exists>d. (Star S b d \<and> S c d)"
proof -
  have "have_diamond_prop S" by (simp add: h2)
  (*have "is_reflex S" by (simp add: h4)*)
  have "Star S a c" by (simp add: h1)
  then obtain d where "Star S b d \<and> S c d"

   \<comment> \<open>Haremos induccion en Star S a c, por lo que consideramos "b" arbitrario\<close>
   \<comment> \<open> Caso refl  tenemos que a = c, ie Star a c \<equiv> Star a a \<close>
   (*
        a
      /   \* = 0
     b     a
    *\?   / ? : si, por hip S a b
        d         
    podemos tomar d = b por reflex de S :  S a a y S b b. Pero para usar eso,
    necesitamos agregar como hipotesis del lema que S es reflex.(?)
   *)
    proof (induction arbitrary:b rule:Star.induct)
      case (refl a)
      have "S a b" by (simp add: h1)
      have "Star S b b" by (simp add: h1)
      then obtain d where "Star S b d" and "S a d" by (simp add: h1)
      then show ?case using local.refl by blast
    next
    (* caso step a c , tenemos por def. de Star que si S a b entonces Star S a b.  
    Aca habría que pensar en subcasos si c es igual o no a b?
        a
      /   \* = 1
     b     c      la def de Star.step nos dice que si S a b entonces Star S a b.
     *\?  /?     
        d
    *)
      case (step a c)
      have "S a b" by (simp add: h1)
      have "S a c" by (simp add: step.hyps)
      have "\<exists>d. S b d \<and> S c d" using h1 by (simp add: have_diamond_prop_def)
      then have  "\<exists>d. Star S b d \<and> S c d" by (simp add: h1)
      then show ?case
      using step.prems by blast
    next
      case (trans a b2 bn)
    (*
           a
        /     \
       b        b2
        \     /    \ 
          d1        \*
             \  HI   bn
            ?*\     /?
                 dn
     En este caso haremos induccion en Star S b2 c. 
    -case refl nos deja como hipotesis  S a b , S a b2 lo que 
    permitiria  aplicar HI usando lo q ya demostramos para step (o aplicar prop diamante).
    -case step nos deja S a b , Star S a c , usar HI   
    *)
      have t0: "S a b" by (simp add: h1)
      have t1: "S a b2" by (simp add: trans.hyps(1))
      have t2: "Star S b2 bn" by (simp add: trans.hyps(2))
      then obtain dn where "Star S b dn" and "S b2 dn"
      proof(induction arbitrary:b rule:Star.induct)
        case (refl a)
        then show ?case by sorry
      next
        case (step a b)
        then show ?case sorry
      next
        case (trans a b c)
        then show ?case sorry
      qed 
      then show ?case using Star.trans
        by auto
    qed
  qed


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
    case (refl x)
      then show ?case by (metis Star.refl)
    next
    
    (*habria que hacer para este caso y el de trans un lema auxiliar que pruebe S a b \<Rightarrow> Star S b c *)
    case (step a b)
      then have "R a b" using assms(1) by blast          (* S contenido en R *)
      note \<open>Star S a b2\<close>
      then obtain c where "Star S b c" and "Star S b2 c"
      proof(induction)
        case (refl a)
          then show ?case using Star.refl by blast
        next
        case (step a b)
          then show ?case by (meson Star.simps)
        next
        case (trans a b c)
           then show ?case using Star.trans by blast
      qed
    next
    case (trans a b c)
      assume "S a b"
      then have "S a b" by simp
      then have "Star S b c" using trans.hyps(2) by blast
      then obtain c' where "Star S c c' \<longrightarrow> Star S b2 c'"
      proof(induction)
        case (refl a)
          then show ?case using Star.refl by blast
        next
        case (step a b)
          then show ?case using Star.refl by blast
        next
        case (trans a b c)
          assume "S a b"
          then have "S a b" by simp
          then have "Star S b c" using trans.hyps(2) by blast
          then obtain c' where "Star S b c'" and "Star S c c'"using Star.refl by blast
          then show ?case using trans.IH trans.prems by blast
        qed        
qed

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