module

public import stacks_project.Chap90.Definition_90_23_1_Smooth

/-!
# Smooth groupoids in functors on the base category

A groupoid in functors on `ArtinianLocalAlgCat Λ k` is smooth when its source and
target maps are smooth morphisms of set-valued functors.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Definition 90.23.1: a groupoid in functors `(U, R, s, t, c)` on
`ArtinianLocalAlgCat Λ k` is smooth if the source and target morphisms
`s, t : R ⟶ U` are smooth as morphisms of set-valued functors. Smoothness
does not depend on the composition `c`. -/
@[stacks 06KI]
class IsSmooth {U R : ArtinianLocalAlgCat Λ k ⥤ Type v} (s t : R ⟶ U) : Prop where
  /-- The source map `s : R ⟶ U` is smooth. -/
  isSmooth_s : NatTrans.IsSmooth s
  /-- The target map `t : R ⟶ U` is smooth. -/
  isSmooth_t : NatTrans.IsSmooth t

/-- The identity groupoid on a functor is smooth. -/
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
