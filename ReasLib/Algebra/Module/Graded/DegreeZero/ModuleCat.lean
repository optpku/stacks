module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Module.Graded.DegreeZero
public import ReasLib.Algebra.Module.GradedNatInt
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero graded pieces in `ModuleCat`

This leaf owns the categorical presentation of a homogeneous piece of an integer-graded module.
The piece is viewed as a module over the degree-zero ring and its subtype inclusion is exposed as
a `ModuleCat` morphism.  The construction is independent of inverse systems and localization, so
degreewise limits and other consumers can share it directly.
-/

@[expose] public section

noncomputable section

universe uA vM

namespace GradedModule

variable {A : Type uA} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The inclusion of an integer-graded degree piece into its ambient module after restricting
scalars to the degree-zero ring.  The source is the canonical `𝒜 0`-module on `𝓧 d` supplied by
`GradedModule.zeroPieceModule`; no synthetic `Submodule (𝒜 0)` copy of the piece is introduced. -/
@[stacks 0EKD "degree-zero module-category component inclusion"]
def degreePieceSubtype
    (X : ModuleCat.{vM} A)
    (𝓧 : ℤ → Submodule ℤ X)
    [SetLike.GradedSMul 𝒜 𝓧]
    (d : ℤ) :
    ModuleCat.of (𝒜 0) (𝓧 d) ⟶
      (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj X :=
  ModuleCat.ofHom
    (X := 𝓧 d)
    (Y := (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj X)
    { toFun := fun x ↦ x.1
      map_add' := sorry
      map_smul' := sorry }

/-- The degree-piece inclusion acts by the underlying subtype inclusion. -/
@[simp, stacks 0EKD "degree-zero module-category inclusion evaluation"]
theorem degreePieceSubtype_apply
    (X : ModuleCat.{vM} A)
    (𝓧 : ℤ → Submodule ℤ X)
    [SetLike.GradedSMul 𝒜 𝓧]
    (d : ℤ) (x : 𝓧 d) :
    degreePieceSubtype 𝒜 X 𝓧 d x = x.1 := sorry

end GradedModule
