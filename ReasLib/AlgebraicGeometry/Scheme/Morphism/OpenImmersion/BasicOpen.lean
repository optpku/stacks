/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsOpenImmersion

/-- Every point in the source of an open immersion into an affine scheme has an affine open
neighborhood whose image is a basic open defined by a global section of the target. -/
theorem exists_affineOpen_mappingTo_basicOpen
    {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U) [IsOpenImmersion i] (w : W) :
    ∃ Wi : W.affineOpens, w ∈ (Wi : W.Opens) ∧ ∃ f : Γ(U, ⊤),
      Scheme.Hom.opensRange ((Wi : W.Opens).ι ≫ i) = U.basicOpen f := by
  let x : Scheme.Hom.opensRange i := ⟨i w, by simp⟩
  obtain ⟨f, hf, hwf⟩ :=
    (isAffineOpen_top U).exists_basicOpen_le x (by simp)
  let Wi : W.affineOpens :=
    (IsOpenImmersion.affineOpensEquiv i).symm
      ⟨⟨U.basicOpen f, (isAffineOpen_top U).basicOpen f⟩, hf⟩
  refine ⟨Wi, ?_, f, ?_⟩
  · change i w ∈ U.basicOpen f
    simpa [x] using hwf
  · have hs :
        (IsOpenImmersion.affineOpensEquiv i) Wi =
          ⟨⟨U.basicOpen f, (isAffineOpen_top U).basicOpen f⟩, hf⟩ := by
        simpa [Wi] using
          (IsOpenImmersion.affineOpensEquiv i).apply_symm_apply
            ⟨⟨U.basicOpen f, (isAffineOpen_top U).basicOpen f⟩, hf⟩
    have hs' : ((IsOpenImmersion.affineOpensEquiv i) Wi).1.1 = U.basicOpen f := by
      simpa using congrArg (fun Z ↦ Z.1.1) hs
    have himage : (Scheme.Hom.opensFunctor i).obj (Wi : W.Opens) = U.basicOpen f :=
      (IsOpenImmersion.affineOpensEquiv_apply_coe_coe i Wi).symm.trans hs'
    simpa [Scheme.Hom.opensRange_comp] using himage

/-- If an affine open maps to a basic open under an open immersion into an affine scheme, then
each basic open inside it also maps to a basic open defined by a global section of the target. -/
theorem exists_basicOpen_mappingTo_basicOpen
    {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U) [IsOpenImmersion i] (Wi : W.affineOpens)
    (f : Γ(U, ⊤)) (hWi : Scheme.Hom.opensRange ((Wi : W.Opens).ι ≫ i) = U.basicOpen f)
    (a : Γ(W, (Wi : W.Opens))) :
    ∃ f' : Γ(U, ⊤), Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) = U.basicOpen f' := by
  let p := (Wi : W.Opens).ι ≫ i
  let ai : Γ(((Wi : W.Opens) : Scheme), ⊤) := ((Wi : W.Opens).topIso.inv) a
  let r : Γ(U, p ''ᵁ (⊤ : (((Wi : W.Opens) : Scheme).Opens))) := (Scheme.Hom.appIso p ⊤).inv ai
  have hp : p ''ᵁ (⊤ : (((Wi : W.Opens) : Scheme).Opens)) = U.basicOpen f := by
    simpa [p, Scheme.Hom.opensRange_comp] using hWi
  let r' : Γ(U, U.basicOpen f) := (U.presheaf.map (eqToHom hp.symm).op) r
  obtain ⟨f', hf'⟩ := (isAffineOpen_top U).basicOpen_basicOpen_is_basicOpen f r'
  refine ⟨f', ?_⟩
  have hsource :
      Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) =
        p ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai) := by
    calc
      Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) = i ''ᵁ W.basicOpen a := by
        simp [Scheme.Hom.opensRange_comp]
      _ = i ''ᵁ ((Wi : W.Opens).ι ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai)) := by
        rw [Scheme.Opens.ι_image_basicOpen_topIso_inv (Wi : W.Opens) a]
      _ = p ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai) := by
        simp [p]
  have himage :
      p ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai) = U.basicOpen r := by
    simpa [p, r] using Scheme.image_basicOpen p ai
  have hr' : U.basicOpen r' = U.basicOpen r := by
    simpa [r'] using Scheme.basicOpen_res_eq U r (eqToHom hp.symm).op
  exact hsource.trans <| himage.trans <| hr'.symm.trans hf'.symm

/-- Given two open immersions from a scheme into affine schemes, every source point has one
affine open neighborhood whose images under both immersions are basic opens. -/
theorem exists_affineOpen_mappingTo_basicOpens
    {U V W : Scheme.{u}} [IsAffine U] [IsAffine V]
    (i : W ⟶ U) (j : W ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j] (w : W) :
    ∃ W' : W.affineOpens, w ∈ (W' : W.Opens) ∧
      ∃ f : Γ(U, ⊤), ∃ g : Γ(V, ⊤),
        Scheme.Hom.opensRange ((W' : W.Opens).ι ≫ i) = U.basicOpen f ∧
          Scheme.Hom.opensRange ((W' : W.Opens).ι ≫ j) = V.basicOpen g := by
  obtain ⟨Wi, hwi, fi, hWi⟩ := exists_affineOpen_mappingTo_basicOpen i w
  obtain ⟨Wj, hwj, fj, hWj⟩ := exists_affineOpen_mappingTo_basicOpen j w
  obtain ⟨a, b, hab, hwa⟩ := exists_basicOpen_le_affine_inter Wi.2 Wj.2 w ⟨hwi, hwj⟩
  obtain ⟨f, hf⟩ := exists_basicOpen_mappingTo_basicOpen i Wi fi hWi a
  obtain ⟨g, hg⟩ := exists_basicOpen_mappingTo_basicOpen j Wj fj hWj b
  have hj : Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ j) = V.basicOpen g := by
    rw [Scheme.Hom.opensRange_comp, hab]
    simpa [Scheme.Hom.opensRange_comp] using hg
  exact ⟨⟨W.basicOpen a, Wi.2.basicOpen a⟩, hwa, f, g, hf, hj⟩

/-- An affine spectrum map is an open immersion exactly when every target prime
is avoided by an element whose induced map on the corresponding principal
localizations is bijective. -/
theorem specMap_iff_exists_awayMap_bijective
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) :
    AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ↔
      ∀ q : PrimeSpectrum A, ∃ f : R,
        φ f ∉ q.asIdeal ∧ Function.Bijective (Localization.awayMap φ f) := sorry

/-- Open immersions between affine spectra induced by ring maps are stable
under composition of the ring maps. -/
theorem specMap_stableUnderComposition :
    RingHom.StableUnderComposition
      (fun {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) ↦
        AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) := sorry

/-- Open immersions between affine spectra induced by ring maps are stable
under base change of the ring maps. -/
theorem specMap_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) ↦
        AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) := sorry

end AlgebraicGeometry.IsOpenImmersion
