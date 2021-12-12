import ..src.lemmas

/-
  The tactics in this file are used to multiply equations by constants and
  add them together.  These helper tactics are used in `linear_combination.lean`
-/



/-
  Given that lhs = rhs, this tactic returns an expr stating that
    coeff * lhs = coeff * rhs

  Input:
    heq : an expr, which should be an equality with some type α on each side,
      where `has_mul α` is true
    coeff : a pexpr, which should be a value of type α
    
  Output: tactic expr that is the result of multiplying both sides of heq by
    the coeff 
-/
meta def mul_equality_expr (heq : expr) (coeff : pexpr) : tactic expr :=
do
  `(%%lhs = %%rhs) ← tactic.infer_type heq,
  -- Explicitly mark the coefficient as having the same type as the sides of
  --   heq - this is necessary in order to use the left_mul_both_sides lemma
  left_type ← tactic.infer_type lhs,
  coeff_expr ← tactic.to_expr ``(%%coeff : %%left_type),
  tactic.mk_app ``left_mul_both_sides [lhs, rhs, coeff_expr, heq]
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'has_mul' condition in order to multiply the " ++
    "equalities by the given factors.")


/-
  Given that a = b and c = d, this tactic returns an expr stating that
    a + c = b + d

  Input:
    heq1 : an expr, which should be an equality with some type α on each side,
      where `has_add α` is true
    heq2 : an expr, which should be an equality with type α on each side
    
  Output: tactic expr that is the result of adding the two equalities
-/
meta def sum_equalities (heq1 heq2 : expr) : tactic expr :=
do
  `(%%lhs1 = %%rhs1) ← tactic.infer_type heq1,
  `(%%lhs2 = %%rhs2) ← tactic.infer_type heq2,
  tactic.mk_app ``sum_two_equations [lhs1, rhs1, lhs2, rhs2, heq1, heq2]
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'has_add' condition in order to add the " ++
    "equalities together.")


/-
  Given that a = b and c = d, along with a coefficient, this tactic returns an
    expr stating that a + coeff * c = b + coeff * d

  Input:
    heq1 : an expr, which should be an equality with some type α on each side,
      where `has_add α` and `has_mul α` are true
    heq2 : an expr, which should be an equality with type α on each side
    coeff_for_eq2 : a pexpr, which should be a value of type α
    
  Output: tactic expr that is the result of adding the first equality to the
    result of multiplying coeff_for_eq2 by the second equality
-/
meta def sum_two_hyps_one_mul_helper (heq1 heq2 : expr) (coeff_for_eq2 : pexpr) :
  tactic expr :=
do
  -- Multiply the second equation by the coefficient
  hmul2 ← mul_equality_expr heq2 coeff_for_eq2,
  -- Add the first equation and the newly computed equation together
  sum_equalities heq1 hmul2


/-
  Builds on the given summed equation by multiplying each equation in the given
    list by its associated coefficient and summing the equations together

  Input:
    option (tactic expr) : none, if there is no sum to add to yet, or some
        containing the base summation equation
    list name : a list of names, referring to equations in the local context
    list pexpr : a list of coefficients to be multiplied with the corresponding
      equations in the list of names
    
  Output: tactic expr expressing the weighted sum of the given equations added
    to the base equation
-/
meta def make_sum_of_hyps_helper :
  option (tactic expr) → list name → list pexpr → tactic expr
| none [] []                                               :=
  do tactic.fail "There are no hypotheses to add"
| (some tactic_hcombo) [] []                               :=
  do tactic_hcombo
| none (heq_nam :: heqs) (coeff :: coeffs)                 :=
 do
    -- This is the first equation, and we do not have anything to add to it
    heq ← tactic.get_local heq_nam,
    let eq1_times_coeff1 := mul_equality_expr heq coeff,
    make_sum_of_hyps_helper (some eq1_times_coeff1) heqs coeffs
| (some tactic_hcombo) (heq_nam :: heqs) (coeff :: coeffs) :=
  do
    heq ← tactic.get_local heq_nam,
    hcombo ← tactic_hcombo,
    -- We want to add this weighted equation to
    --   the current equation in the hypothesis
    let hcombo_updated := sum_two_hyps_one_mul_helper hcombo heq coeff,
    make_sum_of_hyps_helper (some hcombo_updated) heqs coeffs
| _ _ _                                             :=
  do tactic.fail ("The length of the input list of equalities should be the " ++
    "same as the length of the input list of coefficients")


/-
  Given a list of names referencing equalities and a list of pexprs representing
    coefficients, created a weighted sum of the equalities, where each
    equation is multiplied by the corresponding coefficient

  Input:
    heqs : a list of names, referring to equations in the local context
    coeffs : a list of coefficients to be multiplied with the corresponding
      equations in the list of names
    
  Output: tactic expr that is the weighted sum of the equations
-/
meta def make_sum_of_hyps (heqs : list name) (coeffs : list pexpr) : tactic expr :=
do
  make_sum_of_hyps_helper none heqs coeffs
