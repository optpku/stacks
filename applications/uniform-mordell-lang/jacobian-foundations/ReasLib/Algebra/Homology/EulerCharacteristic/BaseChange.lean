/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ReasLib.Algebra.Homology.EulerCharacteristic.Comparison
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Euler characteristic under a supplied scalar-extension comparison

This is the numerical consequence of a cohomology base-change theorem, in any
dimension and for any complex shape. It constructs no cohomology model and does
not assert geometric base change. Its inputs are the actual linear equivalences
from scalar-extended cohomology to the target cohomology.

The tensor product and dimension formula are Mathlib's. This is the same algebraic
dimension transport used in NYLL's `finrank_H1_eq_geometricGenus`, generalized
from a single Čech cokernel to arbitrary graded modules and Euler signs.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace GradedObject

universe u v

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {ι : Type v}

/-- A degreewise scalar-extension comparison preserves Euler characteristic.
For a genuine geometric Euler characteristic, finite-dimensionality and finite
cohomological support must be established separately. -/
theorem eulerChar_eq_of_baseChange (c : ComplexShape ι) [c.EulerCharSigns]
    {X : CategoryTheory.GradedObject ι (ModuleCat k)}
    {Y : CategoryTheory.GradedObject ι (ModuleCat K)}
    (e : ∀ i, K ⊗[k] X i ≃ₗ[K] Y i) :
    eulerChar c X = eulerChar c Y := by
  have hr (i : ι) : Module.finrank k (X i) = Module.finrank K (Y i) := by
    calc
      Module.finrank k (X i) = Module.finrank K (K ⊗[k] X i) :=
        Module.finrank_baseChange.symm
      _ = Module.finrank K (Y i) := (e i).finrank_eq
  unfold eulerChar
  congr 1
  funext i
  rw [hr i]

end GradedObject
