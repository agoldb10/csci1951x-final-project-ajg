import ..src.make_sum_of_hyps
import ..src.simplify
import ..src.match

set_option pp.beta true
set_option pp.generalized_field_notation false


/-
  This file contains the completed tactic and makes use of the remaining Lean
  files in the src folder.
-/


namespace linear_combo

/-
  This is a finishing tactic that attempts to prove the target by
    creating and applying a linear combination of a list of equalities.

  Note: The left and right sides of all the equations should have the same
    ring type, and the coefficients should also have this type.  This type must
    have the has_add, has_mul, and add_group properties.  Also note that
    the target must involve at least one variable.

  Input:
    heqs : a list of names, referring to equations in the local context
    coeffs : a list of coefficients to be multiplied with the corresponding
      equations in the list of names
    
  Output: tactic unit
-/
meta def linear_combination (heqs : list name) (coeffs : list pexpr) : tactic unit :=
  do
    hsum ← make_sum_of_hyps heqs coeffs,
    hsum_on_left ← move_to_left_side hsum,
    move_target_to_left_side,
    normalize_and_match hsum_on_left


section interactive_mode
setup_tactic_parser


/-
  This is the interactive version of a finishing tactic that attempts to prove
    the target by creating and applying a linear combination of a list of
    equalities.  The tactic will create a linear combination by adding the
    equalities together from left to right, so the order of the input hypotheses
    does matter.

  Note: The left and right sides of all the equations should have the same
    type, and the coefficients should also have this type.  This type must
    have the has_add, has_mul, and add_group properties.  Also note that
    the target must involve at least one variable.

  Input:
    heqs : a list of identifiers, referring to equations in the local context
    coeffs : a list of coefficients to be multiplied with the corresponding
      equations in the list of names
    
  Output: tactic unit

  Example Usage:
    Given that h1 and h2 are equalities in the local context
    `linear_combination [h1, h2] [2, -3]`
    will attempt to solve the goal by computing 2 * h1 + -3 * h2
    and matching that to the goal.
-/
meta def _root_.tactic.interactive.linear_combination
  (heqs : parse (list_of ident)) (coeffs : parse pexpr_list) : tactic unit :=
do
  linear_combination heqs coeffs,
  pure ()


end interactive_mode 




end linear_combo