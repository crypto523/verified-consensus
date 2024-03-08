theory Utils
  imports Unsigned Types Invariants
begin

context verified_con
begin

definition enumerate :: "'b list \<Rightarrow> (u64 \<times> 'b) list" where
  "enumerate l \<equiv> zip (map nat_to_u64 [0..<length l]) l"

definition safe_sum :: "u64 set \<Rightarrow> (u64, 'a) cont" where
  "safe_sum s \<equiv> foldrM (.+) (sorted_list_of_set s) 0"

definition var_list_index :: "'b VariableList \<Rightarrow> u64 \<Rightarrow> 'b option" where
  "var_list_index l i \<equiv>
    if i < var_list_len l then
      Some (var_list_inner l ! u64_to_nat i)
    else
      None"

definition var_list_inner :: "'b VariableList \<Rightarrow> 'b list" where
  "var_list_inner l \<equiv> case l of VariableList inner \<Rightarrow> inner"

definition unsafe_var_list_index :: "'b VariableList \<Rightarrow> u64 \<Rightarrow> 'b" where
  "unsafe_var_list_index l i \<equiv> the (var_list_index l i)"

definition vector_index :: "'b Vector \<Rightarrow> u64 \<Rightarrow> 'b option" where
  "vector_index v i \<equiv>
    if i < vector_len v then
      Some (vector_inner v ! u64_to_nat i)
    else
      None"

definition unsafe_vector_index :: "'b Vector \<Rightarrow> u64 \<Rightarrow> 'b" where
  "unsafe_vector_index v i \<equiv> the (vector_index v i)"

definition shift_and_clear_bitvector :: "Config \<Rightarrow> Bitvector \<Rightarrow> Bitvector" where
  "shift_and_clear_bitvector c bv \<equiv>
    Bitvector ([False] @ take (u64_to_nat (JUSTIFICATION_BITS_LENGTH c) - 1) (bitvector_inner bv))"

definition bitvector_update :: "Bitvector \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> Bitvector" where
  "bitvector_update bv i v \<equiv> Bitvector (list_update (bitvector_inner bv) i v)"

definition bitvector_all :: "Bitvector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bitvector_all bv start end \<equiv>
    list_all (\<lambda>x. x) (take (end - start) (drop start (bitvector_inner bv)))"


function integer_squareroot_aux :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> ((u64 \<times> u64), 'a) cont" where
  "integer_squareroot_aux x y n =
    (if y \<ge> x then
      return (x, y)
    else do {
      offset <- n \\ y;
      y' \<leftarrow> y .+ offset;
      integer_squareroot_aux y (y' div 2) n
  })"
  by auto
termination 
  apply (relation "measure (\<lambda>(x,y,n). unat x)") unfolding word_add_def
   apply (clarsimp)
  apply (subst in_measure, clarify)
  apply (clarsimp)
  by (simp add: unat_mono)



(* https://github.com/ethereum/consensus-specs/blob/dev/specs/phase0/beacon-chain.md#integer_squareroot *)
definition integer_squareroot :: "u64 \<Rightarrow> (u64, 'a) cont" where
 "integer_squareroot n = do {
    let x = n;
    x_plus_1 \<leftarrow> x .+ 1;
    y \<leftarrow> x_plus_1 \\ 2;
    (x', _) \<leftarrow> integer_squareroot_aux x y n;
    return x'
  }" 
end
end