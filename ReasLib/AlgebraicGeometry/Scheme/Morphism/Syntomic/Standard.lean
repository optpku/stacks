module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic

/-!
# Standard syntomic scheme morphisms

For morphisms between affine schemes, the standard syntomic condition is the
relative global complete-intersection condition on global sections.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- An affine morphism is standard syntomic when its global-sections ring
homomorphism is a relative global complete intersection. -/
@[stacks 01UC "standard syntomic morphism"]
abbrev StandardSyntomic [IsAffine X] [IsAffine S] : Prop :=
  let _ : Algebra (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) :=
    (CommRingCat.Hom.hom (Scheme.Hom.appTop f)).toAlgebra
  Algebra.IsRelativeGlobalCompleteIntersection
    (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X))

/-- The global-sections map of a standard syntomic affine morphism is a
relative global complete intersection. -/
@[stacks 01UC "relative global complete intersection underlying a standard syntomic morphism"]
theorem standardSyntomic_isRelativeGlobalCompleteIntersection
    [IsAffine X] [IsAffine S] (hf : StandardSyntomic f) :
    let _ : Algebra (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) :=
      (CommRingCat.Hom.hom (Scheme.Hom.appTop f)).toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection
      (Scheme.Γ.obj (Opposite.op S)) (Scheme.Γ.obj (Opposite.op X)) := sorry

/-- The global-sections ring homomorphism of a standard syntomic affine
morphism is syntomic. -/
@[stacks 01UC "coordinate-ring map of a standard syntomic morphism is syntomic"]
theorem standardSyntomic_appTop_syntomic
    [IsAffine X] [IsAffine S] (hf : StandardSyntomic f) :
    RingHom.Syntomic (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) := sorry

/-- A standard syntomic affine morphism is syntomic as a morphism of schemes. -/
@[stacks 01UC "standard syntomic morphism is syntomic"]
theorem standardSyntomic_syntomic
    [IsAffine X] [IsAffine S] (hf : StandardSyntomic f) :
    Syntomic f := sorry

end AlgebraicGeometry
