theory Translation_Test
  imports Cont_Monad_Algebra VerifiedConsensus Helpers "Word_Lib.Word_64" "Word_Lib.More_Arithmetic"
begin

(*

abbreviation (expr_notation)
  write_expr :: "'a \<Rightarrow> 'b \<Rightarrow> (unit, 'c) cont"
  where "write_expr \<equiv> write_to"

nonterminal expr 

term All


syntax
  "_assign_expr" :: "'a \<Rightarrow> expr \<Rightarrow> (unit, 'c) cont " ("_ := _" [1000, 13] 13)
  "_eval_expr"   :: "('d \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> expr \<Rightarrow> expr" ("_ _ _" [1000, 13] 13)
  "_eval_inner"  :: "('d \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> expr" (" _ _ " [1000, 13] 13)
  "_eval_bin_both"    :: "('d \<Rightarrow> 'e \<Rightarrow> 'b) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" (" _ _ _ " [1000, 13] 13)
  "_eval_ref"  :: "'a \<Rightarrow> expr" (" _ ")
  "_eval_val"  :: "'b \<Rightarrow> expr" (" _ ")





abbreviation (input) "with f e \<equiv> bindCont f (\<lambda>b. return (e, b))"  


abbreviation  (input) cont_comp :: "('a \<Rightarrow> ('b, 'r) cont) =>  ('b \<Rightarrow> ('c, 'r) cont) => ('a \<Rightarrow> ('c, 'r) cont)" where 
 "cont_comp f g \<equiv> \<lambda>a. bindCont (f a) g"

abbreviation  (input) "uncurry f \<equiv> (\<lambda>(x,y). f x y)"


abbreviation  (input) compose :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" 
  where "compose f g \<equiv> (\<lambda>x. f (g x))"

term bindCont

 (*  "_expr_final" :: "'b \<Rightarrow> expr" ("_") *)

find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)"
translations
(* "_assign_expr a (_expr_final b)" \<rightharpoonup> "CONST write_expr a b" *)
 "_assign_expr a (_eval_inner f b)" \<rightharpoonup> "_eval_expr f b (_assign_expr a)"
 "_assign_expr a (_eval_bin_both f b c)" \<rightharpoonup> "CONST bindCont (_eval_expr b) (CONST cont_comp (CONST with (_eval_expr c)) (CONST compose (CONST write_to a) (CONST uncurry f)))"

 "(_eval_expr (_eval_ref a))" \<rightharpoonup> "CONST read a"
 "(_eval_expr (_eval_val a))" \<rightharpoonup> "CONST return a"


 "(_eval_expr (_assign_expr a))" \<rightharpoonup> "CONST write_to a"
 "_eval_expr f b e" \<rightharpoonup> "CONST bindCont (CONST read b)  (CONST compose (_eval_expr e) f) " 


definition "foo (x :: u64 Vector) (y :: nat) = (undefined :: nat)"


term "slashings := plus slashings slashings"

term "slashings := plus randao_mixes (foo slashings 1)"
*)

context verified_con
begin

definition set_justified_checkpoint :: "Checkpoint \<Rightarrow> (unit, 'a) cont"
  where "set_justified_checkpoint n \<equiv> (current_justified_checkpoint ::= n)"

definition weigh_justification_and_finalization ::
  "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
where
  "weigh_justification_and_finalization total_active_balance
                                        previous_epoch_target_balance
                                        current_epoch_target_balance \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch  <- get_current_epoch;
     old_previous_justified_checkpoint <- read previous_justified_checkpoint;
     old_current_justified_checkpoint  <- read current_justified_checkpoint;
     _ <- (current_justified_checkpoint ::= old_current_justified_checkpoint);
     bits <- read justification_bits;
     let shifted_justification_bits = shift_and_clear_bitvector config bits;
     _ <- (justification_bits ::= shifted_justification_bits);
     previous_epoch_target_x3 \<leftarrow> previous_epoch_target_balance .* 3;
     current_epoch_target_x3  \<leftarrow> current_epoch_target_balance .* 3;
     total_active_balance_x2  \<leftarrow> total_active_balance .* 2;
     (if previous_epoch_target_x3 \<ge> total_active_balance_x2 then do {
           bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 1 False;
           block_root <- get_block_root previous_epoch;
           _  <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := previous_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)} else return ());
     (if current_epoch_target_x3 \<ge> total_active_balance_x2 then do {
           bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 0 False;
           block_root <- get_block_root previous_epoch;
           _ <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := current_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)} else return ());
     bits <- read justification_bits;
     x <- epoch_f old_previous_justified_checkpoint .+ Epoch 3;
     _ <- (if (bitvector_all bits 1 4 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ()); 
     x <- epoch_f old_previous_justified_checkpoint .+ Epoch 2;
     _ <- (if (bitvector_all bits 1 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     _ <- (if (bitvector_all bits 0 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     (if (bitvector_all bits 0 2 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ())  
     }"

definition process_justification_and_finalization ::
  "(unit, 'a) cont"
where
  "process_justification_and_finalization \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     epoch1 \<leftarrow> GENESIS_EPOCH .+ Epoch 1;
    if current_epoch \<le> epoch1 then
      return ()
    else do {
      previous_indices \<leftarrow> 
        get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX previous_epoch;
      current_indices \<leftarrow>
        get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX current_epoch;
      total_active_balance    \<leftarrow> get_total_active_balance;
      previous_target_balance \<leftarrow> get_total_balance  previous_indices;
      current_target_balance  \<leftarrow> get_total_balance  previous_indices;
      weigh_justification_and_finalization
         total_active_balance previous_target_balance current_target_balance
    }
  }"

(* TODO: rewrite with map *)
definition get_flag_index_deltas ::
  "nat \<Rightarrow> ((u64 list \<times> u64 list), 'a) cont"
where
  "get_flag_index_deltas flag_index \<equiv> do {
    v <- read validators;
    let init_rewards = [0. _ \<leftarrow> [0..<length (var_list_inner v)]];
    let init_penalties = init_rewards;
    previous_epoch <- get_previous_epoch;
    unslashed_participating_indices \<leftarrow> get_unslashed_participating_indices flag_index previous_epoch;
    let weight = PARTICIPATION_FLAG_WEIGHTS ! flag_index;
    unslashed_participating_balance \<leftarrow> get_total_balance unslashed_participating_indices;
    unslashed_participating_increment \<leftarrow> unslashed_participating_balance \\
                                            EFFECTIVE_BALANCE_INCREMENT config;
    total_active_balance \<leftarrow> get_total_active_balance ;
    active_increments \<leftarrow> total_active_balance \\ EFFECTIVE_BALANCE_INCREMENT config;
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices;
    foldrM (\<lambda>index opt. do {
      let (rewards, penalties) = opt;
      base_reward \<leftarrow> get_base_reward index;
      in_inactivity_leak \<leftarrow> is_in_inactivity_leak;
      let index_nat = u64_to_nat index;
      if index \<in> unslashed_participating_indices then (
        if \<not> in_inactivity_leak then do {
          reward_numerator_pre \<leftarrow> base_reward .* weight;
          reward_numerator \<leftarrow> reward_numerator_pre .* unslashed_participating_increment;
          reward_denominator \<leftarrow> active_increments .* WEIGHT_DENOMINATOR;
          reward \<leftarrow> reward_numerator \\ reward_denominator;
          total_reward \<leftarrow> rewards ! index_nat .+ reward;
          let rewards' = list_update rewards index_nat total_reward;
          return (rewards', penalties)
        } else (return (rewards, penalties))

      ) else if flag_index \<noteq> TIMELY_HEAD_FLAG_INDEX then do {
        penalty_pre \<leftarrow> base_reward .* weight;
        penalty \<leftarrow> penalty_pre \\ WEIGHT_DENOMINATOR;
        total_penalty \<leftarrow> penalties ! index_nat .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        return (rewards, penalties')
      } else (return (rewards, penalties))
    })  eligible_validator_indices (init_rewards, init_penalties)
  }"


definition get_inactivity_penalty_deltas ::
  "(u64 list \<times> u64 list, 'a) cont"
where
  "get_inactivity_penalty_deltas \<equiv> do {
    v <- read validators;
    let init_rewards = [0. _ \<leftarrow> [0..<length (var_list_inner v)]];
    let init_penalties = init_rewards;
    previous_epoch <- get_previous_epoch;
    matching_target_indices \<leftarrow> get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX
                                                                   previous_epoch;
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices;
    vs <- read validators;
    scores <- read inactivity_scores; 
    (final_rewards, final_penalties) <- foldrM (\<lambda>index opt. do {
      let (rewards, penalties) = opt;
      let index_nat = u64_to_nat index;
      if index \<notin> matching_target_indices then do {
        validator \<leftarrow> lift_option (var_list_index vs index);
        inactivity_score \<leftarrow> lift_option (var_list_index scores index);
        penalty_numerator \<leftarrow> effective_balance_f validator .* inactivity_score;
        penalty_denominator \<leftarrow> INACTIVITY_SCORE_BIAS config .* INACTIVITY_PENALTY_QUOTIENT_ALTAIR;
        penalty \<leftarrow> penalty_numerator \\ penalty_denominator;
        total_penalty \<leftarrow> (penalties ! index_nat) .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        return (rewards, penalties')}
      else
        return (rewards, penalties)}) eligible_validator_indices (init_rewards, init_penalties);
    return (final_rewards, final_penalties)
  }"

(* TODO: use this more? *)
definition var_list_update ::
  "'b VariableList \<Rightarrow> u64 \<Rightarrow> 'b \<Rightarrow> ('b VariableList, 'a) cont"
  where
  "var_list_update xs i x \<equiv> do {
    if u64_to_nat i < length (var_list_inner xs) then
      return (VariableList (List.list_update (var_list_inner xs) (u64_to_nat i) x))
    else
      fail
  }"

definition increase_balance ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "increase_balance index reward \<equiv> do {
     orig_balances \<leftarrow> read balances;
     orig_balance \<leftarrow> lift_option (var_list_index orig_balances index);
     new_balance \<leftarrow> orig_balance .+ reward;
     new_balances \<leftarrow> var_list_update orig_balances index new_balance;
     balances ::= new_balances
  }"

definition decrease_balance ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "decrease_balance index penalty \<equiv> do {
     orig_balances \<leftarrow> read balances;
     orig_balance \<leftarrow> lift_option (var_list_index orig_balances index);
     let new_balance = nat_to_u64 (u64_to_nat orig_balance - u64_to_nat penalty);
     new_balances \<leftarrow> var_list_update orig_balances index new_balance;
     balances ::= new_balances
  }"

definition apply_rewards_and_penalties 
  where "apply_rewards_and_penalties rp v = do {
      let (rewards, penalties) = rp;
      _ \<leftarrow> mapM (\<lambda>index. do {
        let reward = rewards ! u64_to_nat index;
        let penalty = penalties ! u64_to_nat index;
        _ \<leftarrow> increase_balance index reward;
        decrease_balance index penalty
      }) (map nat_to_u64 [0..<length (var_list_inner v)]);
      return ()
  }"

definition process_rewards_and_penalties ::
  "(unit, 'a) cont"
where
  "process_rewards_and_penalties \<equiv> do {
    v <- read validators;
    current_epoch <- get_current_epoch;
    if current_epoch = GENESIS_EPOCH then return ()
    else do {

    flag_deltas \<leftarrow> foldrM (\<lambda>flag_index all_deltas. do {
      flag_index_deltas \<leftarrow> get_flag_index_deltas flag_index;
      return (all_deltas @ [flag_index_deltas])
    }) [0..<length PARTICIPATION_FLAG_WEIGHTS] [];

    inactivity_penalty_deltas \<leftarrow> get_inactivity_penalty_deltas;
    _ \<leftarrow> mapM (\<lambda>rp. apply_rewards_and_penalties rp v) (flag_deltas @ [inactivity_penalty_deltas]);
    return ()
    }}"

end