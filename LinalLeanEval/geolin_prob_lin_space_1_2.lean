import Mathlib.Data.Matrix.Basic
import Aesop
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.RewriteSearch


def x: List ℚ :=  [6, 2, 9]
def e_1: List ℚ :=  [5, 0, 4]
def e_2: List ℚ :=  [5, -1, 0]
def e_3: List ℚ :=  [-1, 0, 4]

def x1: ℚ := 73/24
def x2: ℚ := -2
def x3: ℚ := -19/24


theorem correctness: List.foldl (List.zipWith (.+.)) (List.map (x1 * .) e_1) [(List.map (x2 * .) e_2), (List.map (x3 * .) e_3)] = x := by
    simp [e_1, e_2, e_3, x, List.zipWith, List.foldl, x1, x2, x3]
    norm_num
