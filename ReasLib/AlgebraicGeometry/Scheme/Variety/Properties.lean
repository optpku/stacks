/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Standard properties of varieties over a field

This leaf packages the standard affine, projective, quasi-projective, proper,
and smooth variants of a variety as thin typeclasses over their canonical
scheme and morphism properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k]

/-- A variety over the field `k` is affine if its underlying scheme is affine. -/
@[stacks 04L1]
class AffineVariety (X : SchemeOverField k) : Prop where
  /-- The underlying variety structure. -/
  toVariety : Variety X
  /-- Affineness of the underlying scheme. -/
  toIsAffine : IsAffine X.left

/-- A variety with affine underlying scheme is an affine variety. -/
@[stacks 04L1, instance]
instance instAffineVariety (X : SchemeOverField k) [Variety X] [IsAffine X.left] :
    AffineVariety X where
  toVariety := inferInstance
  toIsAffine := inferInstance

/-- An affine variety over `k` is a variety over `k`. -/
@[stacks 04L1, instance]
instance instVarietyOfAffineVariety (X : SchemeOverField k) [h : AffineVariety X] :
    Variety X :=
  h.toVariety

/-- An affine variety over `k` has affine underlying scheme. -/
@[stacks 04L1, instance]
instance instIsAffineOfAffineVariety (X : SchemeOverField k) [h : AffineVariety X] :
    IsAffine X.left :=
  h.toIsAffine

/-- Unfold `AffineVariety X` into `Variety X` together with affineness of the underlying scheme. -/
theorem affineVariety_iff (X : SchemeOverField k) :
    AffineVariety X ↔ Variety X ∧ IsAffine X.left := sorry

/-- A variety over the field `k` is projective if its structure morphism to
`Spec (CommRingCat.of k)` is projective. -/
@[stacks 04L1]
class ProjectiveVariety (X : SchemeOverField k) : Prop where
  /-- The underlying variety structure. -/
  toVariety : Variety X
  /-- Projectivity of the structure morphism. -/
  toProjective : Projective X.hom

/-- A variety with projective structure morphism is a projective variety. -/
@[stacks 04L1, instance]
instance instProjectiveVariety (X : SchemeOverField k) [Variety X] [Projective X.hom] :
    ProjectiveVariety X where
  toVariety := inferInstance
  toProjective := inferInstance

/-- A projective variety over `k` is a variety over `k`. -/
@[stacks 04L1, instance]
instance instVarietyOfProjectiveVariety (X : SchemeOverField k) [h : ProjectiveVariety X] :
    Variety X :=
  h.toVariety

/-- A projective variety over `k` has projective structure morphism to `Spec k`. -/
@[stacks 04L1, instance]
instance instProjectiveOfProjectiveVariety (X : SchemeOverField k) [h : ProjectiveVariety X] :
    Projective X.hom :=
  h.toProjective

/-- Unfold `ProjectiveVariety X` into `Variety X` together with projectivity of its structure
morphism. -/
theorem projectiveVariety_iff (X : SchemeOverField k) :
    ProjectiveVariety X ↔ Variety X ∧ Projective X.hom := sorry

/-- A variety over the field `k` is quasi-projective if its structure morphism to
`Spec (CommRingCat.of k)` is quasi-projective. -/
@[stacks 04L1]
class QuasiProjectiveVariety (X : SchemeOverField k) : Prop where
  /-- The underlying variety structure. -/
  toVariety : Variety X
  /-- Quasi-projectivity of the structure morphism. -/
  toQuasiProjective : QuasiProjective X.hom

/-- A variety with quasi-projective structure morphism is a quasi-projective variety. -/
@[stacks 04L1, instance]
instance instQuasiProjectiveVariety
    (X : SchemeOverField k) [Variety X] [QuasiProjective X.hom] :
    QuasiProjectiveVariety X where
  toVariety := inferInstance
  toQuasiProjective := inferInstance

/-- A quasi-projective variety over `k` is a variety over `k`. -/
@[stacks 04L1, instance]
instance instVarietyOfQuasiProjectiveVariety
    (X : SchemeOverField k) [h : QuasiProjectiveVariety X] :
    Variety X :=
  h.toVariety

/-- A quasi-projective variety over `k` has quasi-projective structure morphism to `Spec k`. -/
@[stacks 04L1, instance]
instance instQuasiProjectiveOfQuasiProjectiveVariety
    (X : SchemeOverField k) [h : QuasiProjectiveVariety X] :
    QuasiProjective X.hom :=
  h.toQuasiProjective

/-- Unfold `QuasiProjectiveVariety X` into `Variety X` together with quasi-projectivity of its
structure morphism. -/
theorem quasiProjectiveVariety_iff (X : SchemeOverField k) :
    QuasiProjectiveVariety X ↔ Variety X ∧ QuasiProjective X.hom := sorry

/-- A variety over the field `k` is proper if its structure morphism to
`Spec (CommRingCat.of k)` is proper. -/
@[stacks 04L1]
class ProperVariety (X : SchemeOverField k) : Prop where
  /-- The underlying variety structure. -/
  toVariety : Variety X
  /-- Properness of the structure morphism. -/
  toIsProper : IsProper X.hom

/-- A variety with proper structure morphism is a proper variety. -/
@[stacks 04L1, instance]
instance instProperVariety (X : SchemeOverField k) [Variety X] [IsProper X.hom] :
    ProperVariety X where
  toVariety := inferInstance
  toIsProper := inferInstance

/-- A proper variety over `k` is a variety over `k`. -/
@[stacks 04L1, instance]
instance instVarietyOfProperVariety (X : SchemeOverField k) [h : ProperVariety X] :
    Variety X :=
  h.toVariety

/-- A proper variety over `k` has proper structure morphism to `Spec k`. -/
@[stacks 04L1, instance]
instance instIsProperOfProperVariety (X : SchemeOverField k) [h : ProperVariety X] :
    IsProper X.hom :=
  h.toIsProper

/-- Unfold `ProperVariety X` into `Variety X` together with properness of its structure
morphism. -/
theorem properVariety_iff (X : SchemeOverField k) :
    ProperVariety X ↔ Variety X ∧ IsProper X.hom := sorry

/-- A variety over the field `k` is smooth if its structure morphism to
`Spec (CommRingCat.of k)` is smooth. -/
@[stacks 04L1]
class SmoothVariety (X : SchemeOverField k) : Prop where
  /-- The underlying variety structure. -/
  toVariety : Variety X
  /-- Smoothness of the structure morphism. -/
  toSmooth : Smooth X.hom

/-- A variety with smooth structure morphism is a smooth variety. -/
@[stacks 04L1, instance]
instance instSmoothVariety (X : SchemeOverField k) [Variety X] [Smooth X.hom] :
    SmoothVariety X where
  toVariety := inferInstance
  toSmooth := inferInstance

/-- A smooth variety over `k` is a variety over `k`. -/
@[stacks 04L1, instance]
instance instVarietyOfSmoothVariety (X : SchemeOverField k) [h : SmoothVariety X] :
    Variety X :=
  h.toVariety

/-- A smooth variety over `k` has smooth structure morphism to `Spec k`. -/
@[stacks 04L1, instance]
instance instSmoothOfSmoothVariety (X : SchemeOverField k) [h : SmoothVariety X] :
    Smooth X.hom :=
  h.toSmooth

/-- Unfold `SmoothVariety X` into `Variety X` together with smoothness of its structure
morphism. -/
theorem smoothVariety_iff (X : SchemeOverField k) :
    SmoothVariety X ↔ Variety X ∧ Smooth X.hom := sorry

end

end AlgebraicGeometry
