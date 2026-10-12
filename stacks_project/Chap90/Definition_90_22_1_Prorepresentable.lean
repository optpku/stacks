/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Definition_90_21_4_Functors
public import stacks_project.Chap90.Definition_90_21_7_Restrict

/-!
# Prorepresentable groupoids in functors on the base category

A groupoid in functors on `ArtinianLocalAlgCat` is prorepresentable when it is
isomorphic to the restriction of a representable groupoid in functors on
`CompleteLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace CategoryTheory.GroupoidInFunctors

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Restriction of a groupoid in functors on `CompleteLocalAlgCat` along
`ArtinianLocalAlgCat.inclusion`. -/
def restrictInclusion
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)) :
    GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k) :=
  @restrict.{u + 1, u + 1, u, u, u}
    (CompleteLocalAlgCat Λ k) _ (ArtinianLocalAlgCat Λ k) _ _
    Ghat ArtinianLocalAlgCat.inclusion

/-- Restriction along the inclusion precomposes the object functor with
`ArtinianLocalAlgCat.inclusion`. -/
theorem restrictInclusion_U
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)) :
    (restrictInclusion Ghat).U = ArtinianLocalAlgCat.inclusion ⋙ Ghat.U :=
  sorry

/-- Restriction along the inclusion precomposes the arrow functor with
`ArtinianLocalAlgCat.inclusion`. -/
theorem restrictInclusion_R
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)) :
    (restrictInclusion Ghat).R = ArtinianLocalAlgCat.inclusion ⋙ Ghat.R :=
  sorry

/-- A groupoid in functors on `ArtinianLocalAlgCat Λ k` is prorepresentable if it is
isomorphic to the restriction of a representable groupoid in functors on
`CompleteLocalAlgCat Λ k`. -/
class IsProrepresentable
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) : Prop where
  /-- There exists a representable groupoid on `CompleteLocalAlgCat` whose restriction
  along `ArtinianLocalAlgCat.inclusion` is isomorphic to `G`. -/
  exists_representable :
    ∃ Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k),
      IsRepresentable Ghat ∧ Nonempty (Iso (restrictInclusion Ghat) G)

/-- Prorepresentability means existence of a representable groupoid on
`CompleteLocalAlgCat` whose restriction along the inclusion is isomorphic to `G`. -/
theorem isProrepresentable_iff
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔
      ∃ Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k),
        IsRepresentable Ghat ∧ Nonempty (Iso (restrictInclusion Ghat) G) :=
  sorry

/-- The restriction of a representable groupoid in functors on `CompleteLocalAlgCat` is
prorepresentable. -/
instance instIsProrepresentable_restrict
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [IsRepresentable Ghat] : IsProrepresentable (restrictInclusion Ghat) where
  exists_representable :=
    ⟨Ghat, inferInstance, ⟨Iso.refl (restrictInclusion Ghat)⟩⟩

/-- Prorepresentability is equivalent to existence of objects `R0`, `R1` of
`CompleteLocalAlgCat`, morphisms `src, tgt : R0 ⟶ R1` whose pushout exists, a composition
morphism, identity and inverse maps, and groupoid laws, such that the restriction of the
corresponding coyoneda groupoid is isomorphic to `G`. -/
theorem isProrepresentable_iff_coyoneda
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔
      ∃ (R0 R1 : CompleteLocalAlgCat Λ k) (src tgt : R0 ⟶ R1)
        (hpush : HasPushout src tgt)
        (comp : R1 ⟶ @pushout (CompleteLocalAlgCat Λ k) _ R0 R1 R1 src tgt hpush)
        (idMap : coyoneda.obj (op R0) ⟶ coyoneda.obj (op R1))
        (invMap : coyoneda.obj (op R1) ⟶ coyoneda.obj (op R1))
        (laws : @CoyonedaGroupoidLaws (CompleteLocalAlgCat Λ k) _ R0 R1 src tgt hpush
          comp idMap invMap),
        Nonempty
          (Iso
            (restrictInclusion
              (@ofCoyoneda (CompleteLocalAlgCat Λ k) _ R0 R1 src tgt hpush
                comp idMap invMap laws))
            G) :=
  sorry

/-- Prorepresentability is invariant under isomorphism of groupoids in functors. -/
theorem isProrepresentable_of_iso
    {G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}
    (e : Iso G H) [IsProrepresentable G] : IsProrepresentable H :=
  sorry

end CategoryTheory.GroupoidInFunctors
