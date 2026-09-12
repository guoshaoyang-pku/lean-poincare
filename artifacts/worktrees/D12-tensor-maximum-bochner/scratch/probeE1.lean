import Mathlib.Tactic
abbrev Vec3 := Fin 3 → ℝ
def so3e1 : Vec3 := ![0, 1, 0]
example : so3e1 0 = 0 := rfl
example : so3e1 1 = 1 := rfl
example : so3e1 2 = 0 := rfl
example : (if (0 : Fin 3) = 2 then (1:ℝ) else 0) = 0 := by norm_num
example : (if (1 : Fin 3) = 2 then (1:ℝ) else 0) = 0 := by decide
example : (if (2 : Fin 3) = 1 then (1:ℝ) else 0) = 0 := by simp
example : (if (0 : Fin 3) = 2 then (1:ℝ) else 0) = 0 := by simp
