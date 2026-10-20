/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Saturation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.AffineDescent
public import ReasLib.Topology.Maps.ClosedQuotient

/-!
# Integral descent of invariant affine opens

This module descends invariant affine opens along integral morphisms whose images meet every
orbit of a groupoid scheme.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The pullback-source map is surjective when the image of the object morphism meets every
orbit. -/
lemma targetPullbackSource_surjective {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U)
    (h_meets : ∀ u : G.U.left, ∃ v : U'.left,
      g.left v ∈ G.t.left '' (G.s.left ⁻¹' {u})) :
    Function.Surjective ((Limits.pullback.snd g G.t ≫ G.s).left) := by
  intro u
  rcases h_meets u with ⟨v, r, hr_mem, htr⟩
  obtain ⟨x, hfst, hsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := g.left) (g := G.t.left) v r htr.symm
  let e := CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S) g G.t
  let x' : (Limits.pullback g G.t).left := e.inv x
  have hfst' : Over.Hom.left (Limits.pullback.fst g G.t) x' = v := by
    have hfst'' :=
      congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_fst
        (CategoryTheory.Over.forget S) g G.t) x)
    change Over.Hom.left (Limits.pullback.fst g G.t) x' =
      Limits.pullback.fst g.left G.t.left x at hfst''
    exact hfst''.trans hfst
  have hsnd' : Over.Hom.left (Limits.pullback.snd g G.t) x' = r := by
    have hsnd'' :=
      congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_snd
        (CategoryTheory.Over.forget S) g G.t) x)
    change Over.Hom.left (Limits.pullback.snd g G.t) x' =
      Limits.pullback.snd g.left G.t.left x at hsnd''
    exact hsnd''.trans hsnd
  refine ⟨x', ?_⟩
  change G.s.left (Over.Hom.left (Limits.pullback.snd g G.t) x') = u
  calc
    G.s.left (Over.Hom.left (Limits.pullback.snd g G.t) x') = G.s.left r := by rw [hsnd']
    _ = u := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hr_mem

/-- The canonical saturation of an open is open when its pullback is the corresponding open
preimage and every orbit meets the object morphism. -/
lemma canonicalSaturation_isOpen {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) [IsIntegralHom G.s.left] [IsIntegralHom G.t.left]
    [IsIntegralHom g.left] (W' : Scheme.Opens U'.left)
    (h_meets : ∀ u : G.U.left, ∃ v : U'.left,
      g.left v ∈ G.t.left '' (G.s.left ⁻¹' {u}))
    (h_preimage :
      (Limits.pullback.snd g G.t ≫ G.s).left ⁻¹'
          (G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left)))) =
        (Limits.pullback.fst g G.t).left ⁻¹' (W' : Set U'.left)) :
    IsOpen (G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left)))) := by
  let h : (Limits.pullback g G.t).left ⟶ G.U.left := (Limits.pullback.snd g G.t ≫ G.s).left
  let pr0 : (Limits.pullback g G.t).left ⟶ U'.left := (Limits.pullback.fst g G.t).left
  let snd : (Limits.pullback g G.t).left ⟶ G.R.left := (Limits.pullback.snd g G.t).left
  -- Local instance justification (proof-local temporary data): the orbit-cover hypothesis
  -- supplies surjectivity for the closed-quotient criterion.
  let _ : Surjective h := by
    exact ⟨targetPullbackSource_surjective G g h_meets⟩
  -- Local instance justification (proof-local temporary data): the lower pullback projection
  -- is integral, so the pullback-source morphism is universally closed.
  let _ : IsIntegralHom snd := by
    change IsIntegralHom (Over.Hom.left (Limits.pullback.snd g G.t))
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
    exact (CategoryTheory.MorphismProperty.cancel_left_of_respectsIso
      (P := @IsIntegralHom) (Limits.PreservesPullback.iso (Over.forget S) g G.t).hom
      (Limits.pullback.snd g.left G.t.left)).mpr
        (CategoryTheory.MorphismProperty.pullback_snd (P := @IsIntegralHom)
          g.left G.t.left inferInstance)
  -- Local instance justification (proof-local temporary data): integrality is closed under
  -- composition with the source morphism.
  let _ : IsIntegralHom h := by
    change IsIntegralHom (snd ≫ G.s.left)
    infer_instance
  have h_closed_quotient : IsClosedQuotientMap h := by
    refine ⟨Scheme.Hom.surjective h, Scheme.Hom.continuous h, Scheme.Hom.isClosedMap h⟩
  have h_pullback_open :
      IsOpen
        ((Limits.pullback.snd g G.t ≫ G.s).left ⁻¹'
          (G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left))))) := by
    rw [h_preimage]
    exact W'.2.preimage (Scheme.Hom.continuous pr0)
  exact (h_closed_quotient.isOpen_iff_preimage
      (T := G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left))))).2 h_pullback_open

/-- An open canonical saturation is affine when its pullback is an affine open and every orbit
meets the object morphism. -/
lemma canonicalSaturation_isAffineOpen {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) [IsIntegralHom G.s.left] [IsIntegralHom G.t.left]
    [IsIntegralHom g.left] (W' : Scheme.Opens U'.left) (h_affine : IsAffineOpen W')
    (h_meets : ∀ u : G.U.left, ∃ v : U'.left,
      g.left v ∈ G.t.left '' (G.s.left ⁻¹' {u}))
    (h_preimage :
      (Limits.pullback.snd g G.t ≫ G.s).left ⁻¹'
          (G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left)))) =
        (Limits.pullback.fst g G.t).left ⁻¹' (W' : Set U'.left)) :
    IsAffineOpen
      ⟨G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left))),
        canonicalSaturation_isOpen G g W' h_meets h_preimage⟩ := by
  let h : (Limits.pullback g G.t).left ⟶ G.U.left := (Limits.pullback.snd g G.t ≫ G.s).left
  let pr0 : (Limits.pullback g G.t).left ⟶ U'.left := (Limits.pullback.fst g G.t).left
  let snd : (Limits.pullback g G.t).left ⟶ G.R.left := (Limits.pullback.snd g G.t).left
  let T : Set G.U.left := G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left)))
  let W : Scheme.Opens G.U.left := ⟨T, canonicalSaturation_isOpen G g W' h_meets h_preimage⟩
  -- Local instance justification (proof-local temporary data): the lower pullback projection
  -- is the base change of the integral morphism `g.left`.
  let _ : IsIntegralHom snd := by
    change IsIntegralHom (Over.Hom.left (Limits.pullback.snd g G.t))
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
    exact (CategoryTheory.MorphismProperty.cancel_left_of_respectsIso
      (P := @IsIntegralHom) (Limits.PreservesPullback.iso (Over.forget S) g G.t).hom
      (Limits.pullback.snd g.left G.t.left)).mpr
        (CategoryTheory.MorphismProperty.pullback_snd (P := @IsIntegralHom)
          g.left G.t.left inferInstance)
  -- Local instance justification (proof-local temporary data): the outer pullback projection
  -- is the base change of the integral morphism `G.t.left`.
  let _ : IsIntegralHom pr0 := by
    change IsIntegralHom (Over.Hom.left (Limits.pullback.fst g G.t))
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_fst]
    exact (CategoryTheory.MorphismProperty.cancel_left_of_respectsIso
      (P := @IsIntegralHom) (Limits.PreservesPullback.iso (Over.forget S) g G.t).hom
      (Limits.pullback.fst g.left G.t.left)).mpr
        (CategoryTheory.MorphismProperty.pullback_fst (P := @IsIntegralHom)
          g.left G.t.left inferInstance)
  -- Local instance justification (proof-local temporary data): the pullback-source morphism
  -- is a composite of integral morphisms.
  let _ : IsIntegralHom h := by
    change IsIntegralHom (snd ≫ G.s.left)
    infer_instance
  have h_affine_source : IsAffineOpen (pr0 ⁻¹ᵁ W') := by
    exact h_affine.preimage pr0
  have h_preimage_open : h ⁻¹ᵁ W = pr0 ⁻¹ᵁ W' := by
    ext x
    change
      x ∈ ((Limits.pullback.snd g G.t ≫ G.s).left ⁻¹' T) ↔
        x ∈ ((Limits.pullback.fst g G.t).left ⁻¹' (W' : Set U'.left))
    simpa [T] using congrArg (fun A => x ∈ A) h_preimage
  have h_affine_preimage : IsAffineOpen (h ⁻¹ᵁ W) := by
    rw [h_preimage_open]
    exact h_affine_source
  -- Local instance justification (proof-local temporary data): the orbit-cover hypothesis
  -- supplies the surjectivity used in affine descent.
  let _ : Surjective h := by
    exact ⟨targetPullbackSource_surjective G g h_meets⟩
  -- Local instance justification (proof-local temporary data): surjectivity restricts to the
  -- source and target opens identified by the pullback equality.
  let _ : Surjective (h ∣_ W) := by
    constructor
    intro y
    rcases Scheme.Hom.surjective h y.1 with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa [hx] using y.2
    · exact Subtype.ext (by simpa [hx])
  -- Local instance justification (proof-local temporary data): the domain open is affine by
  -- the identified affine pullback.
  let _ : IsAffine (h ⁻¹ᵁ W) := h_affine_preimage
  change IsAffine W
  exact AlgebraicGeometry.Scheme.isAffine_of_surjective_universallyClosed (f := h ∣_ W)

/-- Pulling the canonical saturation back along the pullback-source map recovers the inverse
image of the original invariant open. -/
lemma preimage_canonicalSaturation_eq_pullbackSourcePreimage {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U) (W' : Scheme.Opens U'.left)
    (h_invariant : (G.toPreRelation.pullback g).IsOpenInvariant W') :
    (Limits.pullback.snd g G.t ≫ G.s).left ⁻¹'
        (G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left)))) =
      (Limits.pullback.fst g G.t).left ⁻¹' (W' : Set U'.left) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨q, hq_source, hq_target⟩
    rcases hq_source with ⟨w', hw', hw'q⟩
    have hw'inv : g.left w' = G.t.left (G.i.left q) := by
      calc
        g.left w' = G.s.left q := hw'q
        _ = G.t.left (G.i.left q) := by
          have hInverseTarget := congr($(congrArg Over.Hom.left G.inverse_target) q)
          simpa [Category.assoc] using hInverseTarget.symm
    obtain ⟨y0, hy0fst, hy0snd⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := g.left) (g := G.t.left) w'
        (G.i.left q) hw'inv
    let e := CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S) g G.t
    let y : (Limits.pullback g G.t).left := e.inv y0
    have hyfst : Over.Hom.left (Limits.pullback.fst g G.t) y = w' := by
      have hyfst' :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_fst
          (CategoryTheory.Over.forget S) g G.t) y0)
      change Over.Hom.left (Limits.pullback.fst g G.t) y =
        Limits.pullback.fst g.left G.t.left y0 at hyfst'
      exact hyfst'.trans hy0fst
    have hysnd : Over.Hom.left (Limits.pullback.snd g G.t) y = G.i.left q := by
      have hysnd' :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_snd
          (CategoryTheory.Over.forget S) g G.t) y0)
      change Over.Hom.left (Limits.pullback.snd g G.t) y =
        Limits.pullback.snd g.left G.t.left y0 at hysnd'
      exact hysnd'.trans hy0snd
    have hy :
        ((Limits.pullback.snd g G.t ≫ G.s).left) y =
          ((Limits.pullback.snd g G.t ≫ G.s).left) x := by
      calc
        ((Limits.pullback.snd g G.t ≫ G.s).left) y = G.s.left (G.i.left q) := by
          simpa [Category.assoc, hysnd]
        _ = G.t.left q := by
          have hInverseSource := congr($(congrArg Over.Hom.left G.inverse_source) q)
          simpa [Category.assoc] using hInverseSource
        _ = ((Limits.pullback.snd g G.t ≫ G.s).left) x := hq_target
    have hy_mem : ((Limits.pullback.fst g G.t).left) y ∈ W' := by
      rwa [hyfst]
    let h : Limits.pullback g G.t ⟶ G.U := Limits.pullback.snd g G.t ≫ G.s
    let P := G.toPreRelation.pullback g
    rw [AlgebraicGeometry.Scheme.PreRelation.isOpenInvariant_iff,
      AlgebraicGeometry.Scheme.PreRelation.isSetInvariant_iff] at h_invariant
    obtain ⟨z0, hz0fst, hz0snd⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := h.left) (g := h.left) y x hy
    let e' := CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S) h h
    let z : (Limits.pullback h h).left := e'.inv z0
    have hzfst : Over.Hom.left (Limits.pullback.fst h h) z = y := by
      have hzfst' :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_fst
          (CategoryTheory.Over.forget S) h h) z0)
      change Over.Hom.left (Limits.pullback.fst h h) z =
        Limits.pullback.fst h.left h.left z0 at hzfst'
      exact hzfst'.trans hz0fst
    have hzsnd : Over.Hom.left (Limits.pullback.snd h h) z = x := by
      have hzsnd' :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_snd
          (CategoryTheory.Over.forget S) h h) z0)
      change Over.Hom.left (Limits.pullback.snd h h) z =
        Limits.pullback.snd h.left h.left z0 at hzsnd'
      exact hzsnd'.trans hz0snd
    let comp : (Limits.pullback (𝟙 U') P.t).left :=
      Over.Hom.left (restrictionComparison G g (𝟙 U')) z
    let q' : P.left.left := Over.Hom.left (Limits.pullback.snd (𝟙 U') P.t) comp
    have hsource : P.s.left q' = (Limits.pullback.fst g G.t).left y := by
      have hsource' :=
        congr($(congrArg Over.Hom.left (restrictionComparison_source G g (𝟙 U'))) z)
      have hsourceStep :
          P.s.left q' =
            (Limits.pullback.fst g G.t).left ((Limits.pullback.fst h h).left z) := by
        exact hsource'
      simpa [hzfst] using hsourceStep
    have htarget : P.t.left q' = (Limits.pullback.fst g G.t).left x := by
      have htarget' :=
        congr($(congrArg Over.Hom.left (restrictionComparison_target G g (𝟙 U'))) z)
      have htargetStep :
          P.t.left q' =
            (Limits.pullback.fst g G.t).left ((Limits.pullback.snd h h).left z) := by
        exact htarget'
      simpa [hzsnd] using htargetStep
    have hsource_mem : P.s.left q' ∈ W' := by
      rwa [hsource]
    have htarget_mem : P.t.left q' ∈ W' := h_invariant q' hsource_mem
    rwa [htarget] at htarget_mem
  · intro hx
    refine ⟨G.i.left ((Limits.pullback.snd g G.t).left x), ?_, ?_⟩
    · refine ⟨(Limits.pullback.fst g G.t).left x, hx, ?_⟩
      calc
        g.left ((Limits.pullback.fst g G.t).left x) =
            G.t.left ((Limits.pullback.snd g G.t).left x) := by
          have hpull :=
            congr($(congrArg Over.Hom.left
              (show Limits.pullback.fst g G.t ≫ g =
                  Limits.pullback.snd g G.t ≫ G.t from Limits.pullback.condition)) x)
          simpa [Category.assoc] using hpull
        _ = G.s.left (G.i.left ((Limits.pullback.snd g G.t).left x)) := by
          have hInverseSource :=
            congr($(congrArg Over.Hom.left G.inverse_source) ((Limits.pullback.snd g G.t).left x))
          simpa [Category.assoc] using hInverseSource.symm
    · have hInverseTarget :=
        congr($(congrArg Over.Hom.left G.inverse_target) ((Limits.pullback.snd g G.t).left x))
      simpa [Category.assoc] using hInverseTarget

/-- An invariant affine open for the pulled-back relation descends along an integral object
morphism meeting every orbit to an invariant affine open containing the image point. -/
theorem exists_invariantAffineOpen_of_pullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) [IsIntegralHom G.s.left] [IsIntegralHom G.t.left]
    [IsIntegralHom g.left]
    (h_meets : ∀ u : G.U.left, ∃ u' : U'.left,
      g.left u' ∈ G.t.left '' (G.s.left ⁻¹' {u}))
    (u' : U'.left) (W' : Scheme.Opens U'.left) (hu' : u' ∈ W')
    (h_affine : IsAffineOpen W')
    (h_invariant : (G.toPreRelation.pullback g).IsOpenInvariant W') :
    ∃ W : Scheme.Opens G.U.left,
      g.left u' ∈ W ∧ IsAffineOpen W ∧ G.toPreRelation.IsOpenInvariant W := by
  let T : Set G.U.left := G.t.left '' (G.s.left ⁻¹' (g.left '' (W' : Set U'.left)))
  have h_preimage :
      (Limits.pullback.snd g G.t ≫ G.s).left ⁻¹' T =
        (Limits.pullback.fst g G.t).left ⁻¹' (W' : Set U'.left) :=
    preimage_canonicalSaturation_eq_pullbackSourcePreimage G g W' h_invariant
  let W : Scheme.Opens G.U.left := ⟨T, canonicalSaturation_isOpen G g W' h_meets h_preimage⟩
  have hW_affine : IsAffineOpen W := by
    simpa [W, T] using canonicalSaturation_isAffineOpen G g W' h_affine h_meets h_preimage
  have huW : g.left u' ∈ W := by
    change g.left u' ∈ T
    refine ⟨G.e.left (g.left u'), ?_, ?_⟩
    · refine ⟨u', hu', ?_⟩
      have h_id_source := congr($(congrArg Over.Hom.left G.identity_source) (g.left u'))
      simpa using h_id_source.symm
    · have h_id_target := congr($(congrArg Over.Hom.left G.identity_target) (g.left u'))
      simpa using h_id_target
  have hW_invariant : G.toPreRelation.IsOpenInvariant W := by
    change G.toPreRelation.IsSetInvariant T
    simpa [T] using GroupoidScheme.isSetInvariant_image_preimage G
      (g.left '' (W' : Set U'.left))
  exact ⟨W, huW, hW_affine, hW_invariant⟩

end AlgebraicGeometry.GroupoidScheme
