module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.GradedHom

/-!
# Shift Comparisons for Tensor and Internal Hom

The two comparisons in this file are generated from the canonical homogeneous identity maps
and the enriched map operations of relative tensor and fixed-source internal Hom.  This makes
the absence of additional signs part of the reusable construction rather than an ambient
`CommShift` assumption.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

/-- The sign-free map from the shift of fixed-source internal Hom to internal Hom into the
shifted target. -/
def internalHomShiftHom (N : DifferentialGradedBimodule.{u, v, x, y} A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHom N P)[k] ⟶ internalHom N (P[k]) :=
  DifferentialGradedModule.Shift.sourceHomEquiv
    (internalHom N P) (internalHom N (P[k])) k
    (internalHomMapClosed N (DifferentialGradedModule.Shift.toGradedHom P k))

/-- The inverse sign-free map from internal Hom into a shifted target to the shift of internal
Hom. -/
def internalHomShiftInv (N : DifferentialGradedBimodule.{u, v, x, y} A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    internalHom N (P[k]) ⟶ (internalHom N P)[k] :=
  DifferentialGradedModule.closedGradedHomEquivShiftHom A
    (internalHom N (P[k])) (internalHom N P) k
    (internalHomMapClosed N (DifferentialGradedModule.Shift.fromGradedHom P k))

/-- Remark 22.30.2 (0FQR): fixed-source internal Hom commutes with shifts of the target,
without an additional sign in the comparison map. -/
@[stacks 0FQR "fixed-source internal Hom commutes with shifts"]
def internalHomShiftIso (N : DifferentialGradedBimodule.{u, v, x, y} A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHom N P)[k] ≅ internalHom N (P[k]) where
  hom := internalHomShiftHom N P k
  inv := internalHomShiftInv N P k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the internal-Hom shift comparison is induced by the homogeneous
identity `P ⟶ P[k]`. -/
theorem internalHomShiftIso_hom (N : DifferentialGradedBimodule.{u, v, x, y} A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHomShiftIso N P k).hom = internalHomShiftHom N P k := sorry

/-- The inverse map of the internal-Hom shift comparison is induced by the homogeneous
identity `P[k] ⟶ P`. -/
theorem internalHomShiftIso_inv (N : DifferentialGradedBimodule.{u, v, x, y} A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHomShiftIso N P k).inv = internalHomShiftInv N P k := sorry

namespace Tensor

variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

/-- The sign-free map from the shift of a relative tensor product to the tensor product with
the shifted first factor. -/
def shiftHom (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (obj M N)[k] ⟶ obj (M[k]) N :=
  DifferentialGradedModule.Shift.sourceHomEquiv (obj M N) (obj (M[k]) N) k
    (mapClosed N (DifferentialGradedModule.Shift.toGradedHom M k))

/-- The inverse sign-free map from the tensor product with a shifted first factor to the shift
of the relative tensor product. -/
def shiftInv (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    obj (M[k]) N ⟶ (obj M N)[k] :=
  DifferentialGradedModule.closedGradedHomEquivShiftHom B
    (obj (M[k]) N) (obj M N) k
    (mapClosed N (DifferentialGradedModule.Shift.fromGradedHom M k))

/-- Remark 22.29.2 (0FQN): relative tensor product commutes with shifts of its first factor,
without an additional sign in the comparison map. -/
@[stacks 0FQN "relative tensor product commutes with shifts"]
def shiftIso (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (obj M N)[k] ≅ obj (M[k]) N where
  hom := shiftHom N M k
  inv := shiftInv N M k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward tensor-shift map is induced by the homogeneous identity `M ⟶ M[k]`. -/
theorem shiftIso_hom (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftIso N M k).hom = shiftHom N M k := sorry

/-- The inverse tensor-shift map is induced by the homogeneous identity `M[k] ⟶ M`. -/
theorem shiftIso_inv (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftIso N M k).inv = shiftInv N M k := sorry

end Tensor

end DifferentialGradedBimodule
