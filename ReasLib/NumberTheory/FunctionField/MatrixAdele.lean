module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import ReasLib.NumberTheory.FunctionField.LocalAdele

/-!
# Local and integral adelic matrices
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Matrix
open Finset TopologicalSpace
open scoped RestrictedProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- Extend a matrix over `O_v` by the identity at every other place. -/
def extendLocalIntegerMatrix (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (completionIntegers X v)) :
    Matrix (Fin n) (Fin n) (integerAdeleRing X) :=
  fun i j w =>
    match Classical.decEq (closedPoints X.left) w v with
    | isTrue h => h.symm ▸ m i j
    | isFalse _ => if i = j then 1 else 0

/-- The `v`-component of `extendLocalIntegerMatrix n X v m` is `m`. -/
theorem extendLocalIntegerMatrix_apply_self (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (completionIntegers X v)) (i j : Fin n) :
    extendLocalIntegerMatrix X n v m i j v = m i j := sorry

/-- Off `v`, `extendLocalIntegerMatrix` is the identity matrix. -/
theorem extendLocalIntegerMatrix_apply_of_ne (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (completionIntegers X v))
    (w : closedPoints X.left) (hw : w ≠ v) (i j : Fin n) :
    extendLocalIntegerMatrix X n v m i j w = if i = j then 1 else 0 := sorry

/-- The group embedding `GL (Fin n) O_v →* GL (Fin n) O` placing a local
integral matrix at `v` and the identity elsewhere. -/
def extendLocalIntegerGL (n : ℕ) (v : closedPoints X.left) :
    GL (Fin n) (completionIntegers X v) →* GL (Fin n) (integerAdeleRing X) where
  toFun u :=
    { val := extendLocalIntegerMatrix X n v u.val
      inv := extendLocalIntegerMatrix X n v u.inv
      val_inv := sorry
      inv_val := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- `extendLocalIntegerGL` acts by `extendLocalIntegerMatrix` on the underlying
matrices. -/
theorem extendLocalIntegerGL_apply (n : ℕ) (v : closedPoints X.left)
    (u : GL (Fin n) (completionIntegers X v)) :
    (extendLocalIntegerGL X n v u).val = extendLocalIntegerMatrix X n v u.val :=
  sorry

/-- The embedding `GL (Fin n) O_v →* GL (Fin n) A` obtained by extending to
integral adeles and applying `GeneralLinearGroup.map` along `O → A`. -/
def localIntegerGL (n : ℕ) (v : closedPoints X.left) :
    GL (Fin n) (completionIntegers X v) →* GL (Fin n) (adeleRing X) :=
  (GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X)).comp
    (extendLocalIntegerGL X n v)

/-- `localIntegerGL` is `GeneralLinearGroup.map` of the local integral extension
along `O → A`. -/
theorem localIntegerGL_apply (n : ℕ) (v : closedPoints X.left)
    (u : GL (Fin n) (completionIntegers X v)) :
    localIntegerGL X n v u =
      GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X)
        (extendLocalIntegerGL X n v u) := sorry

/-- Embed a local matrix at the place `v`, as the identity at every other place. -/
def embedLocalMatrix (n : ℕ) (v : closedPoints X.left)
    (M : Matrix (Fin n) (Fin n) (completion X v)) :
    Matrix (Fin n) (Fin n) (adeleRing X) :=
  open Classical in
    fun i j ↦
      if i = j then
        RestrictedProduct.mulSingle (fun w ↦ completionIntegers X w) v (M i j)
      else RestrictedProduct.single (fun w ↦ completionIntegers X w) v (M i j)

/-- The `v`-component of `embedLocalMatrix` is the original local matrix. -/
theorem embedLocalMatrix_apply (n : ℕ) (v : closedPoints X.left)
    (M : Matrix (Fin n) (Fin n) (completion X v)) (i j : Fin n) :
    embedLocalMatrix X n v M i j v = M i j :=
  sorry

/-- Embed `GL (Fin n) K_v` into `GL (Fin n) A` by the identity at every other
place. -/
def embedLocalGL (n : ℕ) (v : closedPoints X.left)
    (g : GL (Fin n) (completion X v)) : GL (Fin n) (adeleRing X) where
  val := embedLocalMatrix X n v g.val
  inv := embedLocalMatrix X n v g.inv
  val_inv := sorry
  inv_val := sorry

/-- The underlying matrix of `embedLocalGL` is `embedLocalMatrix` of the local
matrix. -/
theorem embedLocalGL_val (n : ℕ) (v : closedPoints X.left)
    (g : GL (Fin n) (completion X v)) :
    (embedLocalGL X n v g).val = embedLocalMatrix X n v g.val := sorry


end AlgebraicGeometry.SchemeOverField
