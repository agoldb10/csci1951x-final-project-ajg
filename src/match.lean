import tactic.ring
import ..src.simplify

/-
  The tactics in this file are used to match the linear combination to the
  goal.  These helper tactics are used in `linear_combination.lean`
-/


/-
  Attempt to match the transformed linear combination and target by
    normalizing both and apply the normalized linear combination to the target

  Input:
    hsum_on_left : expr, which should be an equality whose right side is 0
    norm_mode : a tactic.ring.normalize_mode to pass into tactic.ring.normalize
    
  Output: tactic unit
-/
meta def match_using_norm_mode
  (hsum_on_left : expr) (norm_mode : tactic.ring.normalize_mode) : tactic unit :=
do
  hsum_norm_on_left ← normalize_sum hsum_on_left norm_mode,
  normalize_target norm_mode,
  tactic.apply hsum_norm_on_left,
  pure ()


/-
  Attempt to match the transformed linear combination and target by
    normalizing both and apply the normalized linear combination to the target.
    This method tries different normalization modes to ensure that the
    equalities will match if they are equivalent.
  Although the raw mode may potentially work in all cases, the additional
    modes help create a clearer error message, and some modes are successful in
    certain circumstances while others are not

  Input:
    hsum_on_left : expr, which should be an equality whose right side is 0
    
  Output: tactic unit
-/
meta def normalize_and_match (hsum_on_left : expr) : tactic unit :=
do
  do { match_using_norm_mode hsum_on_left tactic.ring.normalize_mode.raw }
  <|>
  do { match_using_norm_mode hsum_on_left tactic.ring.normalize_mode.SOP }
  <|>
  do { match_using_norm_mode hsum_on_left tactic.ring.normalize_mode.horner }
