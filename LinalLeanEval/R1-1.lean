import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic

def A : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![5, 5, -1],
    ![0, -1, 0],
    ![4, 0, 4]]

def x : Matrix (Fin 3) (Fin 1) ℚ :=
  ![![6], ![2], ![9]]

lemma A_invertible : Matrix.det A ≠ 0 := by
  simp [A, Matrix.det_fin_three]
  norm_num

def coeffs : Matrix (Fin 3) (Fin 1) ℚ :=
  (Matrix.det A)⁻¹ • (Matrix.adjugate A) * x


lemma decomposition :
  let a := (73) / 24
  let b := (-2)
  let c := (-19) / 24
  a • ![5, 0, 4] + b • ![5, -1, 0] + c • ![-1, 0, 4] = ![6, 2, 9] := by
  let a := (73) / 24
  let b := (-2)
  let c := (-19) / 24
  ext i
  fin_cases i <;> simp [a, b, c, Fin.sum_univ_succ, mul_add, mul_comm, mul_left_comm]
  <;> norm_num
  <;> ring_nf
