/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor

/-!
# Smooth groupoids in functors

A groupoid in functors on `ArtinianLocalAlgCat Λ k` is smooth when its source
and target natural transformations are smooth.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- A groupoid in functors is smooth when both of its structure maps are smooth. -/
class IsSmooth {U R : ArtinianLocalAlgCat Λ k ⥤ Type v} (s t : R ⟶ U) : Prop where
  /-- The source map is smooth. -/
  isSmooth_s : NatTrans.IsSmooth s
  /-- The target map is smooth. -/
  isSmooth_t : NatTrans.IsSmooth t

/-- The identity groupoid structure maps are smooth. -/
instance instIsSmoothId {U : ArtinianLocalAlgCat Λ k ⥤ Type v} :
    IsSmooth (𝟙 U) (𝟙 U) :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of both structure
maps. -/
theorem isSmooth_iff {U R : ArtinianLocalAlgCat Λ k ⥤ Type v} (s t : R ⟶ U) :
    IsSmooth s t ↔ NatTrans.IsSmooth s ∧ NatTrans.IsSmooth t :=
  sorry

/-- A smooth groupoid in functors has smooth source and target maps. -/
theorem isSmooth_spec {U R : ArtinianLocalAlgCat Λ k ⥤ Type v} (s t : R ⟶ U)
    [IsSmooth s t] : NatTrans.IsSmooth s ∧ NatTrans.IsSmooth t :=
  sorry

/-- Smoothness of a groupoid in functors implies smoothness of the source map. -/
theorem isSmooth_s {U R : ArtinianLocalAlgCat Λ k ⥤ Type v} (s t : R ⟶ U)
    [IsSmooth s t] : NatTrans.IsSmooth s :=
  sorry

/-- Smoothness of a groupoid in functors implies smoothness of the target map. -/
theorem isSmooth_t {U R : ArtinianLocalAlgCat Λ k ⥤ Type v} (s t : R ⟶ U)
    [IsSmooth s t] : NatTrans.IsSmooth t :=
  sorry

end CategoryTheory.GroupoidInFunctors
