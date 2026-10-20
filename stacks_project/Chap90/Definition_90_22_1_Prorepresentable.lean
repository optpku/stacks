/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable

/-!
# Prorepresentable groupoids in functors on the base category

A groupoid in functors on `ArtinianLocalAlgCat` is prorepresentable when it is
isomorphic to the restriction of a representable groupoid in functors on
`CompleteLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

#check (CategoryTheory.GroupoidInFunctors.restrictInclusion :
  {Λ k : Type u} → [CommRing Λ] → [IsNoetherianRing Λ] → [Field k] →
  [Algebra Λ k] → [Module.Finite Λ k] →
  GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k) →
  GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))

#check (CategoryTheory.GroupoidInFunctors.restrictInclusion_U :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)),
    (GroupoidInFunctors.restrictInclusion Ghat).U =
      ArtinianLocalAlgCat.inclusion ⋙ Ghat.U)

#check (CategoryTheory.GroupoidInFunctors.restrictInclusion_R :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)),
    (GroupoidInFunctors.restrictInclusion Ghat).R =
      ArtinianLocalAlgCat.inclusion ⋙ Ghat.R)

#check (CategoryTheory.GroupoidInFunctors.IsProrepresentable :
  {Λ k : Type u} → [CommRing Λ] → [IsNoetherianRing Λ] → [Field k] →
  [Algebra Λ k] → [Module.Finite Λ k] →
  GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k) → Prop)

#check (CategoryTheory.GroupoidInFunctors.isProrepresentable_iff_restriction :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    GroupoidInFunctors.IsProrepresentable G ↔
      ∃ Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k),
        GroupoidInFunctors.IsRepresentable Ghat ∧
          Nonempty (GroupoidInFunctors.Iso (GroupoidInFunctors.restrictInclusion Ghat) G))

#check (CategoryTheory.GroupoidInFunctors.isProrepresentable_restrict :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [GroupoidInFunctors.IsRepresentable Ghat],
    GroupoidInFunctors.IsProrepresentable (GroupoidInFunctors.restrictInclusion Ghat))

#check (CategoryTheory.GroupoidInFunctors.instIsProrepresentableFunctors :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (U R : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [Functor.IsProrepresentable U] [Functor.IsProrepresentable R],
    GroupoidInFunctors.IsProrepresentableFunctors U R)

#check (CategoryTheory.GroupoidInFunctors.isProrepresentable_iff_coyoneda :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    GroupoidInFunctors.IsProrepresentable G ↔
      ∃ (R0 R1 : CompleteLocalAlgCat Λ k) (src tgt : R0 ⟶ R1)
        (hpush : HasPushout src tgt)
        (comp : R1 ⟶ @pushout (CompleteLocalAlgCat Λ k) _ R0 R1 R1 src tgt hpush)
        (idMap : coyoneda.obj (op R0) ⟶ coyoneda.obj (op R1))
        (invMap : coyoneda.obj (op R1) ⟶ coyoneda.obj (op R1))
        (laws : @GroupoidInFunctors.CoyonedaGroupoidLaws (CompleteLocalAlgCat Λ k) _
          R0 R1 src tgt hpush comp idMap invMap),
        Nonempty
          (GroupoidInFunctors.Iso
            (GroupoidInFunctors.restrictInclusion
              (@GroupoidInFunctors.ofCoyoneda (CompleteLocalAlgCat Λ k) _ R0 R1 src tgt hpush
                comp idMap invMap laws))
            G))

#check (CategoryTheory.GroupoidInFunctors.isProrepresentable_of_iso :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    {G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}
    (e : GroupoidInFunctors.Iso G H) [GroupoidInFunctors.IsProrepresentable G],
    GroupoidInFunctors.IsProrepresentable H)
