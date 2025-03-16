import Mathlib

def row_reduce_matrix (A : Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  A.rowEchelonForm

def row_space_basis (A : Matrix (Fin 4) (Fin 4) ℚ) : List (Matrix (Fin 4) (Fin 1) ℚ) :=
  (row_reduce_matrix A).rows.filter (·.isSome) |>.map some

def A : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.ofLists
    [[1, -1, 1, -1],
     [1, 1, 2, 3],
     [2, 4, 5, 10],
     [2, -4, 1, -6]]

def row_space_basis_A := row_space_basis A
#eval row_space_basis_A

def gram_schmidt (basis : List (Matrix (Fin 4) (Fin 1) ℚ)) : List (Matrix (Fin 4) (Fin 1) ℚ) :=
  let rec gram_schmidt_rec (basis : List (Matrix (Fin 4) (Fin 1) ℚ)) (orthogonal_basis : List (Matrix (Fin 4) (Fin 1) ℚ)) : List (Matrix (Fin 4) (Fin 1) ℚ) :=
    match basis with
    | [] => orthogonal_basis
    | b :: rest =>
      let orthogonal_b := b - (b.dotProduct (orthogonal_basis.last!) / (orthogonal_basis.last!.dotProduct (orthogonal_basis.last!)) * orthogonal_basis.last!)
      gram_schmidt_rec rest (orthogonal_b :: orthogonal_basis)
  gram_schmidt_rec basis []

def orthogonal_basis_A := gram_schmidt row_space_basis_A
#eval orthogonal_basis_A

def orthogonal_complement (basis : List (Matrix (Fin 4) (Fin 1) ℚ)) : List (Matrix (Fin 4) (Fin 1) ℚ) :=
  let n := basis.length
  let id_matrix : Matrix (Fin n) (Fin n) ℚ := Matrix.id n
  let orthogonal_complement_basis : List (Matrix (Fin 4) (Fin 1) ℚ) := (id_matrix.toColumns.map (Matrix.col 1)).toList
  gram_schmidt (orthogonal_complement_basis ++ basis)

def w_basis_A := orthogonal_complement orthogonal_basis_A
#eval w_basis_A

def linear_shell_basis (basis : List (Matrix (Fin 4) (Fin 1) ℚ)) : List (Matrix (Fin 4) (Fin 1) ℚ) :=
  let n := basis.length
  let id_matrix : Matrix (Fin n) (Fin n) ℚ := Matrix.id n
  let linear_shell_basis : List (Matrix (Fin 4) (Fin 1) ℚ) := (id_matrix.toColumns.map (Matrix.col 1)).toList
  gram_schmidt (linear_shell_basis ++ basis)

def l_basis_A := linear_shell_basis w_basis_A
#eval l_basis_A
