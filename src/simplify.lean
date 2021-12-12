import tactic.ring
import ..src.lemmas

/-
  The tactics in this file are used to simplify the linear combination and the
  goal.  These helper tactics are used in `match.lean` and
  `linear_combination.lean`
-/


/-
  Moves all the terms in an equality to the left side of the equals sign by
    subtracting the right side of the equation from the left side.  In other
    words, given lhs = rhs, this tactic returns lhs - rhs = 0

  Input:
    heq : an expr, which should be an equality with some type α on each side,
      where `add_group α` is true
    
  Output: tactic expr that is lhs - rhs = 0, where lhs and rhs are the left and 
    right sides of heq respectively
-/
meta def move_to_left_side (heq : expr) : tactic expr :=
do
  `(%%lhs = %%rhs) ← tactic.infer_type heq,
  tactic.mk_app ``left_minus_right [lhs, rhs, heq]
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'add_group' condition in order to match the linear " ++
    "combination to the target.")


/-
  Moves all the terms in the target to the left side of the equals sign by
    subtracting the right side of the equation from the left side.  In other
    words, given a target of lhs = rhs, this tactic returns lhs - rhs = 0.
  Note: The target must be an equality when this tactic is called, and the
    equality must have some type α on each side, where `add_group α` is true.

  Input: N/A
    
  Output: tactic unit
-/
meta def move_target_to_left_side : tactic unit :=
do
  -- Move all the terms in the target equality to the left side
  target ← tactic.target,
  (targ_lhs, targ_rhs) ← tactic.match_eq target,
  target_left_eq ← tactic.to_expr ``(%%targ_lhs - %%targ_rhs = 0),
  do {
    can_replace_proof ← tactic.mk_app ``all_on_left_equiv [targ_lhs, targ_rhs],
    tactic.replace_target target_left_eq can_replace_proof
  }
  <|> tactic.fail ("The type of the left and right sides of the goal " ++
    "must fulfill the 'add_group' condition in order to match the linear " ++
    "combination to the target.")


/-
  Normalize the given expression using tactic.ring.normalize.  This is used
    to put the linear combination and the target into unique standard forms
    in order to determine if they match

  Input:
    hexpr : an ring expression
    norm_mode : a tactic.ring.normalize_mode to pass into tactic.ring.normalize
    
  Output: a tactic (expr × expr), where the second item in the pair is the
    normalized expression
-/
meta def normalize_expr
  (hexpr : expr) (norm_mode : tactic.ring.normalize_mode) : tactic (expr × expr) :=
do
  tactic.ring.normalize
    tactic.transparency.none
    norm_mode
    hexpr


/-
  Normalize the given linear combination equality.  Since the right side of this
    equality should be 0 at this point, only the left side is normalized.

  Input:
    hsum_left : expr, which should be an equality whose right side is 0
    norm_mode : a tactic.ring.normalize_mode to pass into tactic.ring.normalize
    
  Output: tactic expr, which is the normalized version of hsum_left
-/
meta def normalize_sum
  (hsum_left : expr) (norm_mode : tactic.ring.normalize_mode) : tactic expr :=
do
  -- Normalize the left side of the new linear combination hypothesis
  `(%%heq_lhs_after_move = %%heq_rhs_after_move) ← tactic.infer_type hsum_left,
  (_, hsum_left_simp) ← normalize_expr heq_lhs_after_move norm_mode,
  tactic.rewrite_hyp hsum_left_simp hsum_left


/-
  Normalize the target equality.
  Note: the target must be an equality before calling this tactic

  Input:
    hsum_left : expr, which should be an equality whose right side is 0
    norm_mode : a tactic.ring.normalize_mode to pass into tactic.ring.normalize
    
  Output: tactic unit
-/
meta def normalize_target (norm_mode : tactic.ring.normalize_mode) :
  tactic unit :=
do
  target ← tactic.target,
  (_, target_left_simp) ← normalize_expr target norm_mode,
  target_rw ← tactic.rewrite_target target_left_simp,
  pure ()