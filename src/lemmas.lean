import algebra
import data.real.basic


-- This file contains lemmas that are used in `linear_combination.lean`

lemma left_mul_both_sides {α} [hmul : has_mul α] (x y coeff : α) (h : x = y) :
  coeff * x = coeff * y :=
by apply congr_arg (has_mul.mul coeff) h


lemma sum_two_equations {α} [hadd : has_add α] (x1 y1 x2 y2 : α) (h1 : x1 = y1) (h2: x2 = y2) :
  x1 + x2 = y1 + y2 :=
by convert congr (congr_arg has_add.add h1) h2


lemma left_minus_right {α} [ha : add_group α] (x y : α) (h : x = y) :
  x - y = 0 :=
by apply sub_eq_zero.mpr h


lemma all_on_left_equiv {α} [ha : add_group α] (x y : α) :
  (x = y) = (x - y = 0) :=
begin
  simp,
  apply iff.intro,
  { apply left_minus_right },
  { intro h0,
    exact sub_eq_zero.mp h0 }
end
