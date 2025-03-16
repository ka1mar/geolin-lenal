import Mathlib.Data.Matrix.Basic
import Aesop
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.RewriteSearch

variable (e1 e2 e3: ℚ)

def x: ℚ := 6 * e1 + 2 * e2 + 9 * e3

def e1': ℚ := 5 * e1 + 4 * e3
def e2': ℚ := 5 * e1 - e2
def e3': ℚ := - e1 + 4 * e3

variable (x1 x2 x3 : ℚ)

axiom x_axiom: x e1 e2 e3 = x1 * e1' e1 e3 + x2 * e2' e1 e2 + x3 * e3' e1 e3

-- Определения матрицы перехода и обратной
def transformation_matrix: Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![5, 5, -1], ![0, -1, 0], ![4, 0, 4]]
def transformation_matrix_rev : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![1/6, 5/6, 1/24], ![0, -1, 0], ![-1/6, -5/6, 5/24]]

-- Проверка, что переход в новый базис правильный
theorem transformation_matrix_theorem: ![e1' e1 e3, e2' e1 e2, e3' e1 e3] = Matrix.vecMul ![e1, e2, e3] transformation_matrix := by
  simp [x_axiom, transformation_matrix, e1', e2', e3']
  ext i
  fin_cases i
  <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  <;> ring_nf

-- костыль, чтобы считать рациональные числа
theorem y (x y: ℚ): Mul.mul x y = x * y := by rfl

-- Проверка, что матрицы взаимнообратные
theorem matrix_rev: transformation_matrix * transformation_matrix_rev = Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] := by
  simp [transformation_matrix, transformation_matrix_rev]
  ext i j
  fin_cases i
  <;> fin_cases j
  <;> simp [HMul.hMul, dotProduct, Fin.sum_univ_succ]
  <;> simp [y]
  <;> norm_num


-- Проверка итогового ответа
theorem x': Matrix.mulVec transformation_matrix_rev ![6, 2, 9] = ![73/24, -2, -19/24] := by
  simp [transformation_matrix_rev]
  ext i
  fin_cases i
  <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> norm_num
