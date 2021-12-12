import ..src.linear_combination

set_option trace.app_builder true


-- Simple Cases with ℤ and two or less equations

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by linear_combination [h1] [1]

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  2*x + 4 = -6 :=
by linear_combination [h1] [2]

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination [h1, h2] [1, -2]

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  2*x + 4 - y = -16 :=
by linear_combination [h1, h2] [2, -1]

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by linear_combination [h2, h1] [-1, 2]

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  11*y = -11 :=
by linear_combination [h1, h2] [-2, 3]

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y = 11 :=
by linear_combination [h1, h2] [2, -3]

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y = 11 + 1 - 1 :=
by linear_combination [h1, h2] [2, -3]

example (x y : ℤ) (h1 : 10 = 3*x + 2*y) (h2 : 3 = 2*x + 5*y) :
  11 + 1 - 1 = -11*y :=
by linear_combination [h1, h2] [2, -3]


-- More complicated cases with two equations

example (x y : ℚ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y + 1 = 11 + 1 :=
by linear_combination [h1, h2] [2, -3]

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) :
  b = 2 / 3 :=
by linear_combination [ha, hab] [1/6, 1/3]

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
  b = 2 / 3 :=
by linear_combination [ha, hab, hignore] [1/6, 1/3, 0]



-- Cases with more than 2 equations

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 :=
by linear_combination [ha, hb, hc] [1, -1, -2]

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  6*x = -10 :=
by linear_combination [ha, hb, hc] [1, 4, -3]

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  10 = 6*-x :=
by linear_combination [ha, hb, hc] [1, 4, -3]

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
by linear_combination [h1, h2, h3] [2, 1, -2]

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a :=
by linear_combination [h1, h2, h3, h4] [2, -1, 3, -3]

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  6 - 3*c + 3*a + 3*d = 2*b - d + 12 - 3*a :=
by linear_combination [h2, h3, h1, h4] [2, -1, 3, -3]



-- Cases that should fail

-- This should fail because there are no hypotheses given
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination [] []

-- This should fail because h1 does not have a corresponding coefficient
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
by linear_combination [h1] []

-- This should fail because h2 does not have a corresponding coefficient
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
by linear_combination [h1, h2] [1]

-- This should fail because the first coefficient does not have a corresponding
--   equality
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
by linear_combination [] [1]

-- This should fail because the second coefficient does not have a corresponding
--   equality
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
by linear_combination [h1] [1, 0]

-- This should fail because the second coefficient has a different type than
--   the equations it is being combined with.  This was a design choice for the
--   sake of simplicity, but the tactic could potentially be modified to allow
--   this behavior.
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
by linear_combination [h1, h2] [1, (0 : ℝ)]

-- This should fail because the second coefficient has a different type than
--   the equations it is being combined with.  This was a design choice for the
--   sake of simplicity, but the tactic could potentially be modified to allow
--   this behavior.
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
by linear_combination [h1, h2] [1, (0 : ℕ)]

-- This should fail because the coefficients are incorrect.  They should instead
--   be -2 and 3, respectively.
example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  11*y = -11 :=
by linear_combination [h1, h2] [2, -3]

-- This should fail because the hypothesis and their coefficients are given in
--   the wrong order.  Switching h1 and h2 along with 2 and -1 would fix this
--   issue.  The tactic could potentially be modified to adapt to this
--   behavior and not depend on the order of the lists.
example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  - y + 2*x + 4 = -16 :=
by linear_combination [h1, h2] [2, -1]

-- This fails because the linear_combination tactic requires the equations
--   and coefficients to use a type that fulfills the add_group condition,
--   and ℕ does not.
example (a b : ℕ) (h1 : a = 3) :
  a = 3 :=
by linear_combination [h1] [(1 : ℕ)]

