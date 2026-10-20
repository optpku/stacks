module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard.MorphismProperty

/-!
# Target loci of scheme-morphism properties

This module defines the largest candidate open in the target of a scheme
morphism on which a given morphism property holds, together with its locality
and standard-topology base-change interfaces.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace CategoryTheory.MorphismProperty

variable (P : MorphismProperty Scheme.{u}) {X Y Y' : Scheme.{u}}

/-- The supremum of the target opens over which `f` has property `P`. -/
def targetLocus (f : X ⟶ Y) : Y.Opens :=
  sSup {U : Y.Opens | P (f ∣_ U)}

/-- A point belongs to `P.targetLocus f` exactly when it belongs to some target
open over which the restriction of `f` has property `P`. -/
theorem mem_targetLocus (f : X ⟶ Y) (y : Y) :
    y ∈ P.targetLocus f ↔ ∃ U : Y.Opens, y ∈ U ∧ P (f ∣_ U) := sorry

/-- Every target open over which the restriction of `f` has property `P` is
contained in `P.targetLocus f`. -/
theorem targetLocus_maximal (f : X ⟶ Y) (U : Y.Opens)
    (hU : P (f ∣_ U)) : U ≤ P.targetLocus f := sorry

/-- For a Zariski-local target property, `P.targetLocus f` is the greatest
target open over which the restriction of `f` has property `P`. -/
theorem targetLocus_isGreatest [IsZariskiLocalAtTarget P] (f : X ⟶ Y) :
    IsGreatest {U : Y.Opens | P (f ∣_ U)} (P.targetLocus f) := sorry

/-- For a Zariski-local target property, the target locus is all of the target
exactly when the original morphism has the property. -/
theorem targetLocus_eq_top_iff [IsZariskiLocalAtTarget P] (f : X ⟶ Y) :
    P.targetLocus f = ⊤ ↔ P f := sorry

/-- For a non-Zariski standard topology, a target-local property has
`P.targetLocus f` as its greatest good target open. -/
theorem targetLocus_isGreatest_nonZariski
    (τ : StandardTopology) (h_tau : τ ≠ .zariski)
    [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y) :
    IsGreatest {U : Y.Opens | P (f ∣_ U)} (P.targetLocus f) := sorry

/-- If `g` belongs to the morphism property of a non-Zariski standard
topology and the pullback of `f` along `g` has `P`, then the range of `g` lies
in `P.targetLocus f`. -/
theorem range_subset_targetLocus_nonZariski
    (τ : StandardTopology) (h_tau : τ ≠ .zariski)
    [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : τ.precoverage.morphismProperty g)
    (hf : P (pullback.snd f g)) :
    Set.range g ⊆ P.targetLocus f := sorry

/-- The target locus of a property local for a non-Zariski standard topology
commutes with pullback along a morphism belonging to that topology. -/
theorem targetLocus_preimage_nonZariski
    (τ : StandardTopology) (h_tau : τ ≠ .zariski)
    [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : τ.precoverage.morphismProperty g) :
    g ⁻¹ᵁ P.targetLocus f = P.targetLocus (pullback.snd f g) := sorry

/-- Pulling a target locus back along any member of a non-Zariski standard
cover gives the target locus of the corresponding base change. -/
theorem targetLocus_preimage_cover_nonZariski
    (τ : StandardTopology) (h_tau : τ ≠ .zariski)
    [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y)
    (𝒰 : Scheme.Cover τ.precoverage Y) (i : 𝒰.I₀) :
    𝒰.f i ⁻¹ᵁ P.targetLocus f =
      P.targetLocus (pullback.snd f (𝒰.f i)) := sorry

/-- Target loci are unchanged after precomposing by an isomorphism of source schemes. -/
theorem targetLocus_eq_of_comp_left_iso
    [P.RespectsIso] {X X' Y : Scheme.{u}} (e : X ⟶ X') [IsIso e]
    {f : X ⟶ Y} {f' : X' ⟶ Y} (he : e ≫ f' = f) :
    P.targetLocus f = P.targetLocus f' := by
  ext y
  change (y ∈ P.targetLocus f ↔ y ∈ P.targetLocus f')
  rw [P.mem_targetLocus f y, P.mem_targetLocus f' y]
  constructor
  · rintro ⟨U, hyU, hU⟩
    have hcomp₀ : P ((e ≫ f') ∣_ U) := by
      subst f
      simpa using hU
    have hcomp : P (e ∣_ f' ⁻¹ᵁ U ≫ f' ∣_ U) := by
      simpa [morphismRestrict_comp] using hcomp₀
    exact ⟨U, hyU,
      (MorphismProperty.cancel_left_of_respectsIso
        P (e ∣_ f' ⁻¹ᵁ U) (f' ∣_ U)).mp hcomp⟩
  · rintro ⟨U, hyU, hU⟩
    have he' : inv e ≫ f = f' := by
      simpa [he] using IsIso.inv_hom_id_assoc e f'
    have hcomp₀ : P ((inv e ≫ f) ∣_ U) := by
      subst f'
      simpa using hU
    have hcomp : P (inv e ∣_ f ⁻¹ᵁ U ≫ f ∣_ U) := by
      simpa [morphismRestrict_comp] using hcomp₀
    exact ⟨U, hyU,
      (MorphismProperty.cancel_left_of_respectsIso
        P (inv e ∣_ f ⁻¹ᵁ U) (f ∣_ U)).mp hcomp⟩

/-- For a non-Zariski standard topology, the pullback of a target locus depends only on the
cartesian square and not on the chosen pullback model. -/
theorem targetLocus_preimage_of_isPullback_nonZariski
    (τ : StandardTopology) (hτ : τ ≠ .zariski)
    [P.IsLocalAtTarget τ.precoverage]
    {X Y Y' X' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {i : X' ⟶ X} {f' : X' ⟶ Y'} (hpb : IsPullback i f' f g)
    (hg : τ.precoverage.morphismProperty g) :
    g ⁻¹ᵁ P.targetLocus f = P.targetLocus f' := by
  calc
    g ⁻¹ᵁ P.targetLocus f = P.targetLocus (pullback.snd f g) := by
      simpa using P.targetLocus_preimage_nonZariski τ hτ f g hg
    _ = P.targetLocus f' := by
      symm
      exact P.targetLocus_eq_of_comp_left_iso
        hpb.isoPullback.hom hpb.isoPullback_hom_snd

/-- Pulling back a target locus along an open immersion gives the target locus of the
pullback. -/
theorem targetLocus_preimage_pullbackSnd_zariski
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] :
    g ⁻¹ᵁ P.targetLocus f = P.targetLocus (pullback.snd f g) := by
  ext y
  change (g y ∈ P.targetLocus f ↔ y ∈ P.targetLocus (pullback.snd f g))
  rw [P.mem_targetLocus (pullback.snd f g) y, P.mem_targetLocus f (g y)]
  constructor
  · rintro ⟨U, hyU, hU⟩
    refine ⟨g ⁻¹ᵁ U, hyU, ?_⟩
    have hpbU := Scheme.Hom.isPullback_resLE (H := IsPullback.of_hasPullback f g)
      (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
      (hUST := le_rfl) (hUSX := le_rfl)
      (UY := pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U))
      (hUY := by
        ext x
        constructor
        · intro hx
          have hcomp :
              f ((pullback.fst f g) x) = g ((pullback.snd f g) x) := by
            change ((pullback.fst f g ≫ f) x) = ((pullback.snd f g ≫ g) x)
            exact congrArg (fun k => k x) (pullback.condition (f := f) (g := g))
          exact ⟨by simpa [hcomp] using hx, hx⟩
        · rintro ⟨hx, hy⟩
          exact hy)
    have hpbU' :
        IsPullback
          ((pullback.fst f g).resLE (f ⁻¹ᵁ U) (pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U))
            (by
              change pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U)
              intro x hx
              have hcomp :
                  f ((pullback.fst f g) x) = g ((pullback.snd f g) x) := by
                change ((pullback.fst f g ≫ f) x) = ((pullback.snd f g ≫ g) x)
                exact congrArg (fun k => k x) (pullback.condition (f := f) (g := g))
              simpa [hcomp] using hx))
          ((pullback.snd f g) ∣_ (g ⁻¹ᵁ U))
          (f ∣_ U)
          (g ∣_ U) := by
      simpa [← Scheme.Hom.resLE_eq_morphismRestrict] using hpbU
    exact MorphismProperty.IsLocalAtTarget.of_isPullback_zariski (P := P) hpbU' hU
  · rintro ⟨V, hyV, hV⟩
    refine ⟨g ''ᵁ V, ?_, ?_⟩
    · change g y ∈ g '' V
      exact ⟨y, hyV, rfl⟩
    have hPullbackRestrict : P (pullback.snd (pullback.snd f g) V.ι) := by
      have hV' := hV
      rw [← Scheme.Opens.opensRange_ι V] at hV'
      exact (P.arrow_mk_iso_iff
        (morphismRestrictOpensRange (pullback.snd f g) V.ι)).mp hV'
    have hPullbackImage : P (pullback.snd f (V.ι ≫ g)) := by
      rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f g V.ι).hom,
        pullbackLeftPullbackSndIso_hom_snd]
      exact hPullbackRestrict
    have hImage : P (f ∣_ (g ''ᵁ V)) := by
      have hImage' : P (f ∣_ (V.ι ≫ g).opensRange) := by
        exact (P.arrow_mk_iso_iff
          (morphismRestrictOpensRange f (V.ι ≫ g))).mpr hPullbackImage
      rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι] at hImage'
      exact hImage'
    exact hImage

/-- For Zariski-local target properties, a cartesian open-immersion pullback preserves
target loci independently of the chosen pullback model. -/
theorem targetLocus_preimage_of_isPullback_zariski
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    {X Y Y' X' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {i : X' ⟶ X} {f' : X' ⟶ Y'} [IsOpenImmersion g]
    (hpb : IsPullback i f' f g) :
    g ⁻¹ᵁ P.targetLocus f = P.targetLocus f' := by
  calc
    g ⁻¹ᵁ P.targetLocus f = P.targetLocus (pullback.snd f g) := by
      simpa using P.targetLocus_preimage_pullbackSnd_zariski f g
    _ = P.targetLocus f' := by
      symm
      exact P.targetLocus_eq_of_comp_left_iso
        hpb.isoPullback.hom hpb.isoPullback_hom_snd

end CategoryTheory.MorphismProperty
