import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

def x : Matrix (Fin 3) (Fin 1) ℚ := ![![6, 2, 9]]ᵀ
def e₁ : Matrix (Fin 3) (Fin 1) ℚ := ![![5, 0, 4]]ᵀ
def e₂ : Matrix (Fin 3) (Fin 1) ℚ := ![![5, -1, 0]]ᵀ
def e₃ : Matrix (Fin 3) (Fin 1) ℚ := ![![-1, 0, 4]]ᵀ

-- Create a matrix with the basis vectors as columns
def basisMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  ![
    ![5, 5, -1],
    ![0, -1, 0],
    ![4, 0, 4]
  ]

-- We need to solve the system basisMatrix * c = x
-- From the equations:
-- 5c₁ + 5c₂ - c₃ = 6    (first component)
-- -c₂ = 2                (second component)
-- 4c₁ + 4c₃ = 9          (third component)

-- From the second equation, we get c₂ = -2
def c₂ : ℚ := -2

-- Substitute c₂ into the first equation:
-- 5c₁ + 5(-2) - c₃ = 6
-- 5c₁ - 10 - c₃ = 6
-- 5c₁ - c₃ = 16 ... (Eq. 1)

-- From the third equation:
-- 4c₁ + 4c₃ = 9
-- c₁ + c₃ = 9/4 ... (Eq. 2)

-- From Eq. 2: c₃ = 9/4 - c₁
-- Substitute into Eq. 1:
-- 5c₁ - (9/4 - c₁) = 16
-- 5c₁ - 9/4 + c₁ = 16
-- 6c₁ = 16 + 9/4
-- 6c₁ = 64/4 + 9/4 = 73/4
-- c₁ = 73/24

def c₁ : ℚ := 73 / 24

-- From Eq. 2:
-- c₃ = 9/4 - c₁ = 9/4 - 73/24 = 54/24 - 73/24 = -19/24
def c₃ : ℚ := -19 / 24

-- Define the coefficient vector
def c : Matrix (Fin 3) (Fin 1) ℚ := ![![c₁, c₂, c₃]]ᵀ

-- Verify that basisMatrix * c = x
def verifyManually : Bool :=
  basisMatrix * c = x

-- Calculate the linear combination explicitly
def decomposition : Matrix (Fin 3) (Fin 1) ℚ :=
  c₁ • e₁ + c₂ • e₂ + c₃ • e₃

-- Compute the actual values to verify
def explicitComponent1 : ℚ := 5 * c₁ + 5 * c₂ - 1 * c₃
def explicitComponent2 : ℚ := 0 * c₁ - 1 * c₂ + 0 * c₃
def explicitComponent3 : ℚ := 4 * c₁ + 0 * c₂ + 4 * c₃

-- Show that the components match our expected result
theorem explicit_components_correct :
  explicitComponent1 = 6 ∧ explicitComponent2 = 2 ∧ explicitComponent3 = 9 := by
  unfold explicitComponent1 explicitComponent2 explicitComponent3
  simp [c₁, c₂, c₃]
  norm_num
