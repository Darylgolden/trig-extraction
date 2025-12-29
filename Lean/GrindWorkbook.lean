import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Geometry.Euclidean.Triangle
open Real

variable (x y : ℝ)

grind_pattern cos_sq_add_sin_sq => cos x
grind_pattern cos_sq_add_sin_sq => sin x

grind_pattern Real.tan_eq_sin_div_cos => tan x
grind_pattern Real.tan_eq_sin_div_cos => sin x
grind_pattern Real.tan_eq_sin_div_cos => cos x

grind_pattern Real.sin_neg => sin (-x)
grind_pattern Real.sin_neg => -sin x

grind_pattern Real.cos_neg => cos x
grind_pattern Real.cos_neg => cos (-x)

grind_pattern Real.sin_antiperiodic => sin (Real.pi)
grind_pattern Real.cos_antiperiodic => cos (Real.pi)
grind_pattern Real.tan_periodic => tan (Real.pi)

-- some parts of TR3
grind_pattern Real.sin_periodic => sin (2 * Real.pi)
grind_pattern Real.cos_periodic => cos (2 * Real.pi)


-- TR4
grind_pattern Real.sin_zero => sin 0
grind_pattern Real.cos_zero => cos 0
grind_pattern Real.tan_zero => tan 0
grind_pattern Real.sin_pi_div_six => sin (Real.pi / 6)
grind_pattern Real.cos_pi_div_six => cos (Real.pi / 6)
grind_pattern Real.tan_pi_div_six => tan (Real.pi / 6)
grind_pattern Real.sin_pi_div_four => sin (Real.pi / 4)
grind_pattern Real.cos_pi_div_four => cos (Real.pi / 4)
grind_pattern Real.tan_pi_div_four => tan (Real.pi / 4)
grind_pattern Real.sin_pi_div_three => sin (Real.pi / 3)
grind_pattern Real.cos_pi_div_three => cos (Real.pi / 3)
grind_pattern Real.tan_pi_div_three => tan (Real.pi / 3)
grind_pattern Real.sin_pi_div_two => sin (Real.pi / 2)
grind_pattern Real.cos_pi_div_two => cos (Real.pi / 2)


grind_pattern Real.sin_sq_eq_half_sub => sin x ^ 2
grind_pattern Real.sin_sq_eq_half_sub => cos (2 * x)

-- TR8
grind_pattern Real.two_mul_sin_mul_cos => sin x * cos y
grind_pattern Real.two_mul_cos_mul_cos => cos x * cos y
grind_pattern Real.two_mul_sin_mul_sin => sin x * sin y

-- TR9
-- grind_pattern Complex.sin_add_sin => sin x + sin y idk why this isn't added as a real theorem, need to update mathlib
grind_pattern Real.sin_sub_sin => sin x - sin y
grind_pattern Real.cos_add_cos => cos x + cos y
grind_pattern Real.cos_sub_cos => cos x - cos y

-- TR10
grind_pattern Real.cos_add => cos (x + y)
grind_pattern Real.sin_add => sin (x + y)
grind_pattern Real.cos_sub => cos (x - y)
grind_pattern Real.sin_sub => sin (x - y)
grind_pattern Real.cos_add => cos x * cos y
grind_pattern Real.cos_add => sin x * sin y
grind_pattern Real.sin_add => sin x * cos y
grind_pattern Real.sin_add => cos x * sin y
grind_pattern Real.cos_sub => cos x * cos y
grind_pattern Real.cos_sub => sin x * sin y
grind_pattern Real.sin_sub => sin x * cos y
grind_pattern Real.sin_sub => cos x * sin y

-- TR11
grind_pattern Real.sin_two_mul => sin (2 * x)
grind_pattern Real.sin_two_mul => sin x * cos x
grind_pattern Real.cos_two_mul => cos (2 * x)
grind_pattern Real.cos_two_mul => cos x ^ 2 - sin x ^ 2
grind_pattern Real.cos_two_mul' => cos (2 * x)
grind_pattern Real.cos_two_mul' => cos x ^ 2

-- TR12
-- grind_pattern Real.tan_add => tan (x + y)
-- grind_pattern Real.tan_add => tan x
-- grind_pattern Real.tan_add => tan y
-- grind_pattern Real.tan_sub => tan (x - y)
-- grind_pattern Real.tan_sub => tan x
-- grind_pattern Real.tan_sub => tan y

@[grind]
nonrec theorem sin_add_sin : Real.sin x + Real.sin y =
 2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) :=
  Complex.ofReal_injective <| by simp [Complex.sin_add_sin]

example : x + x = 2 * x := by
  grind

example : (42 : ℚ) / (4) + (42) / (4) + (42) / (4) = (63 / 2) := by
  grind

example : Real.sin (2) * Real.cos (1) + Real.cos (2) * Real.sin (1) =
 Real.sin (3 : ℕ) := by grind


lemma TR2_test_1 : Real.tan x = Real.sin x / Real.cos x :=
  by grind

lemma TR2_test_3 : Real.tan (Real.tan x - Real.sin x / Real.cos x) = 0 :=
  by grind

lemma TR2i_test_1 : Real.sin x / Real.cos x = Real.tan x :=
  by grind

-- sympy tests taken from https://github.com/sympy/sympy/blob/16fa855354eb7bcabd3fe10993841e03b1382692/sympy/simplify/tests/test_trigsimp.py
example : 1 - (Real.sin x)^2 = (Real.cos x)^2 := by grind
-- Pythagorean identities
example : 1 - (sin x)^2 = (cos x)^2 := by grind
example : 1 - (cos x)^2 = (sin x)^2 := by grind
example : (sin x)^2 + (cos x)^2 = 1 := by grind

-- need additional assumptions
example : (cos x ≠ 0) -> ((cos x)^2 ≠ 0) -> 1 + (tan x)^2 = 1/(cos x)^2 := by grind

example : (cos x ≠ 0) -> ((cos x)^2 ≠ 0) -> 1/(cos x)^2 - 1 = (tan x)^2 := by grind

example : (cos x ≠ 0) -> ((cos x)^2 ≠ 0) -> 1/(cos x)^2 - (tan x)^2 = 1 := by grind

-- example : 1 + cot(x)**2 = 1/sin(x)**2 := by grind
-- example : 1/sin(x)**2 - 1 = 1/tan(x)**2 := by grind
-- example : 1/sin(x)**2 - cot(x)**2 = 1 := by grind

example : 5*(cos x)^2 + 5*(sin x)^2 = 5 := by grind
example : 5*(cos (x/2))^2 + 2*(sin (x/2))^2 = 3*cos (x)/2 + 7/2 := by grind

example : (sin x)/(cos x) = tan x := by grind
example : (cos x ≠ 0) -> 2*(tan x)*(cos x) = 2*(sin x) := by grind
-- example : cot(x)**3*sin(x)**3 = cos(x)**3 := by grind
example : (cos x ≠ 0) -> ((cos x)^2 ≠ 0) ->
  (sin x ≠ 0) -> ((sin x)^2 ≠ 0) -> y*(tan x)^2/(sin x)^2 = y/(cos x)^2 := by grind
-- example : cot(x)/cos(x) = 1/sin(x) := by grind

example : sin (x + y) + sin (x - y) = 2*sin (x)*cos (y) := by grind
example : sin (x + y) - sin (x - y) = 2*sin (y)*cos (x) := by grind
example : cos (x + y) + cos (x - y) = 2*cos (x)*cos (y) := by grind
example : cos (x + y) - cos (x - y) = -2*sin (x)*sin (y) := by grind
example : tan (x + y) - tan (x)/(1 - tan (x)*tan (y)) = sin (y)/(-sin (y)*tan (x) + cos (y)) := by grind -- FAIL

-- example : sinh(x + y) + sinh(x - y) = 2*sinh(x)*cosh(y) := by grind
-- example : sinh(x + y) - sinh(x - y) = 2*sinh(y)*cosh(x) := by grind
-- example : cosh(x + y) + cosh(x - y) = 2*cosh(x)*cosh(y) := by grind
-- example : cosh(x + y) - cosh(x - y) = 2*sinh(x)*sinh(y) := by grind
-- example : tanh(x + y) - tanh(x)/(1 + tanh(x)*tanh(y)) = sinh(y)/(sinh(y)*tanh(x) + cosh(y)) := by grind
example : sin (4 * x) = 4*((-sin (x)^2 + cos (x)^2)*sin (x)*cos (x)) := by grind

-- these tests taken from https://github.com/sympy/sympy/blob/16fa855354eb7bcabd3fe10993841e03b1382692/sympy/simplify/tests/test_fu.py

example : cos 1 * cos 3 + sin 1 * sin 3 = cos 2 := by grind
example : cos 1 * cos 3 - sin 1 * sin 3 = cos 4 := by grind
example : cos 1 * sin 3 - sin 1 * cos 3 = sin 2 := by grind -- FAIL
example : cos 1 * sin 3 + sin 1 * cos 3 = sin 4 := by grind
example : cos 1 * sin 3 + sin 1 * cos 3 + 7 = sin 4 + 7 := by grind
example : cos 1 * sin 3 + sin 1 * cos 3 + cos 3 = cos 3 + sin 4 := by grind
example : 2 * cos 1 * sin 3 + 2 * sin 1 * cos 3 + cos 3 = 2 * sin 4 + cos 3 := by grind
example : cos 2 * cos 3 + sin 2 * (cos 1 * sin 2 + cos 2 * sin 1) = cos 1 := by grind -- FAIL

example : (cos 2 * cos 3 + sin 2 * (cos 1 * sin 2 + cos 2 * sin 1)) * cos 5 + sin 1 * sin 5 = cos 4 := by grind -- FAIL

example : Real.sqrt 2 * cos x * x + Real.sqrt 6 * sin x * x = 2 * Real.sqrt 2 * x * sin (x + Real.pi / 6) := by grind -- FAIL
example : cos x / Real.sqrt 6 + sin x / Real.sqrt 2 + cos x / Real.sqrt 6 / 3 + sin x / Real.sqrt 2 / 3 = 4 * Real.sqrt 6 * sin (x + Real.pi / 6) / 9 := by grind -- FAIL
example : cos x / Real.sqrt 6 + sin x / Real.sqrt 2 + cos y / Real.sqrt 6 / 3 + sin y / Real.sqrt 2 / 3 = Real.sqrt 6 * sin (x + Real.pi / 6) / 3 + Real.sqrt 6 * sin (y + Real.pi / 6) / 9 := by grind -- FAIL
example : cos x + Real.sqrt 3 * sin x + 2 * Real.sqrt 3 * cos (x + Real.pi / 6)
= 4 * cos x := by grind
example : cos x + Real.sqrt 3 * sin x + 2 * Real.sqrt 3 * cos (x + Real.pi / 6) + 4 * sin x = 4 * Real.sqrt 2 * sin (x + Real.pi / 4) := by grind -- FAIL

example : cos 2 * sin 3 + sin 2 * cos 4 = sin 2 * cos 4 + sin 3 * cos 2 := by norm_num
