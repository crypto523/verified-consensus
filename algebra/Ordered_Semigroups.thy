theory Ordered_Semigroups
  imports Downset
begin


lemma le_bottom_bottom_le:"x \<le> bottom y \<Longrightarrow> bottom y \<le> x"
  by (metis in_down_bot_trans in_down_iff preorder_bot_class.bot_least)


lemma omega_mono: "x \<le> y \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> x \<in> \<Omega>"
  using order_trans by auto


locale ordered_semigroup = lower_galois_connections + upper_galois_connections +
  fixes f :: "'a :: preorder_bot \<Rightarrow> 'a \<Rightarrow> 'a" constrains less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono_f: " (x :: 'a :: preorder_bot) \<le> y \<Longrightarrow>  a \<le> b \<Longrightarrow> f x a \<le> f y b"
  assumes assoc: "f a (f b c) \<le> f (f a b) c" and assoc': "f a (f b c) \<ge> f (f a b) c" 
  assumes bot_idemp: "\<And>x. bottom x \<le> f (bottom x) (bottom x)"

begin

lift_definition convolute :: "('a downset \<Rightarrow> 'a downset \<Rightarrow> 'a downset)" is
 "\<lambda>A B. (\<Squnion>a\<in>A. \<Squnion>b\<in> B. \<down> (f a  b))"
 apply (clarsimp simp:preorder_class.downset_set_def preorder_class.downset_set_def eta_def)
  apply (intro set_eqI conjI iffI; clarsimp?)
    apply (clarsimp simp: in_down_iff)
  using dual_order.trans apply blast
  using dual_order.trans apply blast
  by (meson bot_idemp in_down_iff in_omega order_refl order_trans subset_iff)

(*
definition "convolute' A B = (\<lambda>c. Sup {A a \<sqinter> B b | a b. c \<le> f a b})"

lift_definition f_conv :: "('a downset \<Rightarrow> 'a downset \<Rightarrow> 'a downset)" is
 "\<lambda>A B.  (Collect) (convolute' (\<lambda>a. a \<in> A) (\<lambda>b. b \<in> B))"
  apply (safe; (clarsimp simp: down_sup_distrib convolute'_def preorder_class.downset_set_def)?)
  apply (meson refine_trans)
   apply (blast)
  oops
   apply blast+
  done
*)
sublocale conv_semi: semigroup convolute
  apply (standard)
  apply (transfer)
  apply (simp)
  apply ( clarsimp simp: mono_f sup_down_down rewrite_sup assoc)
  apply (subst rewrite_sup, clarsimp simp: le_fun_def mono_f)
  apply (safe; clarsimp simp: in_down_iff)
  using assoc' dual_order.trans apply blast
  using assoc dual_order.trans by blast

(*

lemma "convolute = f_conv"
  apply (intro ext, transfer, clarsimp simp: convolute'_def)
  apply (safe)
   apply (clarsimp simp: in_down_iff)
   apply (blast)
   apply (clarsimp simp: in_down_iff)
  apply (blast)
  done

*)
end
(*
locale ordered_monoid = monoid + ordered_semigroup
begin
lift_definition  dnil :: " 'a downset" is "\<down>z" by (clarsimp)


sublocale conv_monoid: monoid convolute dnil
  apply (standard; transfer; clarsimp simp: down_sup_distrib)
    apply (intro set_eqI iffI; clarsimp simp: in_down_iff elim!: in_downsetI )
  oops
    apply (metis left_neutral mono_f preorder_class.order.trans preorder_class.order_refl)
   apply (rule_tac x=z in bexI; clarsimp)
   apply (blast)
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff elim!: in_downsetI )
    apply (metis right_neutral mono_f preorder_class.order.trans preorder_class.order_refl)
  by (metis in_down_iff preorder_class.order_refl right_neutral)

end
*)
locale top_strict = semigroup + top + 
  constrains f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a :: top" and top :: 'a 
  assumes top_strict : "f \<top> x = \<top>"

locale top_semigroup = ordered_semigroup +
  assumes aborting: "\<exists>y\<ge>x. f y (bottom x) \<ge> x"  

begin


lemma mono_conv: "mono (convolute c)"
  apply (clarsimp simp: order_class.mono_def, clarsimp simp: less_eq_downset_def, transfer, clarsimp)
  apply (blast)
  done

lemma conv_bot: "convolute \<top> \<bottom> = \<top> \<Longrightarrow> convolute \<top> c = \<top>"
  apply (rule antisym)
   apply fastforce
  apply (rule preorder_class.dual_order.trans[where b="convolute \<top> \<bottom>"]) 
  using mono_conv order_bot_class.bot.extremum order_class.monoD apply blast
  by (clarsimp)

sublocale conv_top_strict: top_strict convolute \<top>
  apply (standard)
  apply (rule conv_bot)
  apply (transfer, clarsimp)
  apply (intro set_eqI iffI; clarsimp)
  apply (clarsimp simp: in_down_iff)
  using aborting 
  by (meson in_omega order_refl)


end



(* locale top_monoid = monoid + top_semigroup *)

lemma [simp]: "\<exists>x\<in>\<eta> y. P x \<longleftrightarrow> P y" by (clarsimp simp: eta_def)

locale bot_strict = top_semigroup +
  assumes bot_annihilate_seq: "f (bottom x) (y :: 'a) \<le>  (bottom x) "

context bot_strict begin

sublocale top_semigroup ..

lemma bot_annihilate_eq[simp]: "f (bottom x) x \<le> (bottom x)" 
  by (meson bot_annihilate_seq order_bot_class.bot.extremum preorder_class.dual_order.trans)

end


locale plus_times = plus + times +
  constrains times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"


locale exchange_semigroup = plus_times +
  constrains times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a :: ord" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
   assumes exchange: " ( plus (times x y) (times x'  y')) \<le> (times (plus x x') ( plus y y')) "


locale exchange_semigroup_ordered =  
    exchange_semigroup +    ordered_semigroup plus + 
                         t: ordered_semigroup times 


begin

sublocale exchange_convolute: exchange_semigroup convolute t.convolute  
  apply (standard)
  apply (clarsimp simp: less_eq_downset_def)
  apply (transfer)
    apply (clarsimp simp: down_sup_distrib)
  apply (clarsimp simp: in_down_iff)
  by (meson exchange mono_f preorder_class.dual_order.trans preorder_class.order_refl in_down_iff)
  
  
end

locale ab_ordered_semigroup =  ordered_semigroup + 
  assumes commute: "f a b \<le> f b a"
begin

sublocale ab_convolute: abel_semigroup convolute
  apply (standard; transfer, clarsimp simp: down_sup_distrib)
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
  by (metis order_trans commute)+

sublocale conv_sync: abstract_sync convolute
  apply (standard; transfer)
  apply (clarsimp simp: down_sup_distrib)
   apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (meson equals0I)
   apply (clarsimp simp: Bex_def in_down_iff)
  apply (metis ex_in_conv in_omega insert_absorb insert_subset)

  apply (elim disjE; clarsimp?)
   apply blast
  apply (clarsimp simp: Bex_def in_down_iff)
  by (meson bot_idemp in_mono in_omega order_refl order_trans)

end


locale left_monoid = semigroup + 
 fixes z :: 'a ("\<^bold>1") 
 assumes left_neutral [simp]: "z \<^bold>* a = a"

locale right_monoid = semigroup + 
 fixes z :: 'a ("\<^bold>1") 
 assumes right_neutral [simp]: "a \<^bold>* \<^bold>1 = a"

locale unital_semigroup = ordered_semigroup +
  fixes unit_of :: "'a \<Rightarrow> 'a" ("(_\<^sub>1)" [1000] 999)
  assumes unit_of_unit: "\<And>a. a \<le> f a (unit_of a)"
  assumes down_unit: "\<And> a b. x \<le> f b (unit_of a) \<Longrightarrow> x \<le> b \<or> x \<in> \<Omega>" 
  assumes bot_le_unit_bot: "bottom x \<le> unit_of (bottom x)" 
begin


lift_definition dunit :: "'a downset" is "\<Down>(range unit_of) "
  apply (clarsimp)
  apply (clarsimp simp: downset_set_def')
  by (rule_tac x="bottom y" in exI, erule order_trans, rule bot_le_unit_bot)

lemma unit_of_apply: "a \<le> f a (unit_of a)"
  by (subst unit_of_unit, rule)



sublocale conv_right: right_monoid convolute dunit
  apply (standard)
  apply (transfer)
   apply (clarsimp simp:  down_sup_distrib )
  apply (safe; clarsimp simp: in_down_iff down_image_iff )
   defer
  apply (meson UNIV_I down_image_iff order_eq_refl unit_of_unit)
 apply (drule order_trans, rule mono_f, rule order_refl, assumption) 
  apply (drule down_unit; elim disjE)
  using in_downsetI apply blast
  by blast

end


locale left_unital_semigroup = ordered_semigroup + 
  fixes unit_of :: "'a \<Rightarrow> 'a" ("(\<^sub>1_)" [1000] 999)
  assumes unit_of_unit: "(unit_of a) \<le> b \<longleftrightarrow> a \<le> f b a"
  assumes down_unit: "x \<le> f (unit_of a) b \<Longrightarrow> x \<le> b \<or> x \<in> \<Omega>"
begin


lemma bot_le_unit_bot: "bottom x \<le> unit_of (bottom x)"
  by (meson bot_idemp in_down_bot_trans in_down_iff preorder_bot_class.bot_least unit_of_unit)

lift_definition dlunit :: " 'a downset" is "\<Down>(range unit_of) "
  apply (clarsimp)
  apply (clarsimp simp: downset_set_def')
  by (rule_tac x="bottom y" in exI, erule order_trans, rule bot_le_unit_bot)


sublocale conv_left: left_monoid convolute dlunit
  apply (standard)
  apply (transfer)
   apply (clarsimp simp:  down_sup_distrib)
  apply (safe; clarsimp simp: in_down_iff downset_set_def')
   apply (drule order_trans, rule mono_f, assumption, rule order_refl) 
   apply (drule down_unit; elim disjE)
    apply blast
  apply blast
  by (metis preorder_class.order_refl unit_of_unit)

end


(* locale covering_semigroup = ordered_semigroup + 
  assumes covering: "x \<le> f a b \<Longrightarrow> x \<le> a \<or> x \<le> b" *)
 
context monoid begin

sublocale left: left_monoid 
  by (standard, clarsimp)

sublocale right: right_monoid
  by (standard, clarsimp)

end

locale sync_semigroup = unital_semigroup  + ab_ordered_semigroup
begin

sublocale abel_conv: abel_semigroup convolute 
  by (simp add: ab_convolute.abel_semigroup_axioms)

sublocale sync_conv_monoid: monoid convolute dunit
  apply (standard)
  using conv_sync.sync_commute apply auto[1]
  using conv_sync.sync_commute apply auto[1]
  done

end

end