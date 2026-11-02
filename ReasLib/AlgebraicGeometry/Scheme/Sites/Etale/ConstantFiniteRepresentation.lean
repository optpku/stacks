/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite constant sheaves on the small étale slice

For an affine object `U`, a finite set is represented by the spectrum of the
finite product of the global section ring. The inverse sheaf map glues the labels
on the disjoint component cover, allowing different labels on disconnected tests.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Etale.ConstantFiniteRepresentation

variable {X : Scheme.{u}} (U : X.Etale) [IsAffine U.left]
variable (E : Type (u + 1)) [Finite E]

/-- The spectrum of `Nat.card E` copies of the affine ring maps to `U`.
When `E` is finite, its factors may be indexed by the labels in `E`. -/
def structureMap : Spec (.of (Fin (Nat.card E) → Γ(U.left, ⊤))) ⟶ U.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤)
    (Fin (Nat.card E) → Γ(U.left, ⊤)))) ≫ U.left.isoSpec.inv

omit [Finite E] in
set_option backward.isDefEq.respectTransparency false in
instance structureMap_etale : Etale (structureMap U E) := by
  letI : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤))).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  change Etale (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤)))) ≫ U.left.isoSpec.inv)
  infer_instance

omit [Finite E] in
set_option backward.isDefEq.respectTransparency false in
instance structureMap_finite : IsFinite (structureMap U E) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤))))) := by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤))).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  change IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤)))) ≫ U.left.isoSpec.inv)
  infer_instance

/-- The finite product spectrum as an object of the small étale slice at `U`. -/
def object : Over U :=
  Over.mk (MorphismProperty.Over.homMk (structureMap U E) (by rfl) :
    Scheme.Etale.mk (structureMap U E ≫ U.hom) ⟶ U)

variable {E} (labels : E ≃ Fin (Nat.card E))

/-- The branch labelled by `e` is induced by evaluation at its finite index. -/
def component (e : E) : U.left ⟶ (object U E).left.left :=
  U.left.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))
      (labels e)))

set_option backward.isDefEq.respectTransparency false in
/-- Each branch is a section of the structure map. -/
theorem component_structureMap (e : E) : component U labels e ≫ structureMap U E = 𝟙 U.left := by
  have heval :
      CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) (Fin (Nat.card E) → Γ(U.left, ⊤))) ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))
          (labels e)) = 𝟙 _ := by
    ext x
    rfl
  dsimp only [component, structureMap]
  rw [Category.assoc, ← Spec.map_comp_assoc, heval, Spec.map_id]
  change U.left.isoSpec.hom ≫ (𝟙 (Spec (.of Γ(U.left, ⊤))) ≫ U.left.isoSpec.inv) = 𝟙 U.left
  exact (congrArg (fun arrow : Spec (.of Γ(U.left, ⊤)) ⟶ U.left ↦
    U.left.isoSpec.hom ≫ arrow) (Category.id_comp U.left.isoSpec.inv)).trans
      U.left.isoSpec.hom_inv_id

/-- The branch inclusion is a morphism from the terminal object of the slice. -/
def inclusion (e : E) : Over.mk (𝟙 U) ⟶ object U E :=
  Over.homMk (MorphismProperty.Over.homMk (component U labels e) (by
    change component U labels e ≫ (structureMap U E ≫ U.hom) = U.hom
    rw [← Category.assoc, component_structureMap, Category.id_comp])) (by
    apply MorphismProperty.Over.Hom.ext
    exact component_structureMap U labels e)

instance inclusion_mono (e : E) : Mono (inclusion U labels e) :=
  ⟨fun first second _ ↦ Over.mkIdTerminal.hom_ext first second⟩

/-- The covering cofan of the finite product spectrum has one affine branch per label. -/
def cofan : Cofan fun _ : E ↦ Over.mk (𝟙 U) :=
  Cofan.mk (object U E) (inclusion U labels)

set_option backward.isDefEq.respectTransparency false in
/-- The finite product spectrum is covered by its evaluation branches. -/
theorem covering : Sieve.ofArrows _ (cofan U labels).inj ∈
    (X.smallEtaleTopology.over U) (object U E) := by
  rw [(X.smallEtaleTopology).mem_over_iff, Sieve.overEquiv_ofArrows]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro point
  obtain ⟨⟨index, prime⟩, hprime⟩ :=
    (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))).surjective point
  obtain ⟨preimage, hpreimage⟩ := U.left.isoSpec.hom.homeomorph.surjective prime
  change U.left.isoSpec.hom preimage = prime at hpreimage
  refine Set.mem_iUnion.mpr ⟨labels.symm index, preimage, ?_⟩
  change (U.left.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))
      (labels (labels.symm index))))) preimage = point
  rw [Scheme.Hom.comp_apply, hpreimage, Equiv.apply_symm_apply, Spec.map_apply]
  exact hprime

set_option backward.isDefEq.respectTransparency false in
/-- Two distinct labels have empty intersection in the étale slice. -/
theorem disjoint {i j : E} (hij : i ≠ j) {V : Over U}
    (a : V ⟶ Over.mk (𝟙 U)) (b : V ⟶ Over.mk (𝟙 U))
    (hab : a ≫ (cofan U labels).inj i = b ≫ (cofan U labels).inj j) :
    (⊥ : Sieve V) ∈ (X.smallEtaleTopology.over U) V := by
  have hempty : IsEmpty V.left.left := ⟨fun point ↦ by
    have heq := congrArg (fun arrow : V ⟶ object U E ↦ arrow.left.left point) hab
    change (a.left.left ≫ component U labels i) point =
      (b.left.left ≫ component U labels j) point at heq
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at heq
    change PrimeSpectrum.comap
        (Pi.evalRingHom (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤)) (labels i))
          (U.left.isoSpec.hom (a.left.left point)) =
      PrimeSpectrum.comap
        (Pi.evalRingHom (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤)) (labels j))
          (U.left.isoSpec.hom (b.left.left point)) at heq
    have hprime : PrimeSpectrum.sigmaToPi
        (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))
          ⟨labels i, U.left.isoSpec.hom (a.left.left point)⟩ =
        PrimeSpectrum.sigmaToPi (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))
          ⟨labels j, U.left.isoSpec.hom (b.left.left point)⟩ := heq
    have hindex := congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_injective _) hprime)
    exact hij (labels.injective hindex)⟩
  rw [(X.smallEtaleTopology).mem_over_iff, map_bot]
  let emptyArrows : (index : Fin 0) → V.left ⟶ V.left := fun index ↦ Fin.elim0 index
  have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff emptyArrows).mpr
    (Set.eq_univ_of_forall fun point ↦ isEmptyElim point)
  simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using h

set_option backward.isDefEq.respectTransparency false in
/-- The finite constant sheaf is represented by the actual finite product spectrum.
The inverse is the amalgamation of local component labels, including on disconnected tests. -/
def iso [HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] :
    (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E ≅
      (X.smallEtaleTopology.over U).sheafifiedRepresentable (object U E) := by
  letI : ∀ i, Mono ((cofan U labels).inj i) := fun i ↦
    inferInstanceAs (Mono (inclusion U labels i))
  let J := X.smallEtaleTopology.over U
  have hcompat (s : Cofan fun _ : E ↦ J.uliftSheafifiedRepresentable.{u + 1} (Over.mk (𝟙 U))) :
      (J.sheafifiedRepresentableCoconeFamily.{u + 1, u + 1, u} (cofan U labels) s).Compatible := by
    intro Y₁ Y₂ Z first second f₁ f₂ h₁ h₂ hcomm
    have hfac : (first ≫ Sieve.ofArrows.h h₁) ≫ (cofan U labels).inj (Sieve.ofArrows.i h₁) =
        (second ≫ Sieve.ofArrows.h h₂) ≫ (cofan U labels).inj (Sieve.ofArrows.i h₂) := by
      simpa only [Category.assoc, Sieve.ofArrows.fac] using hcomm
    by_cases hidx : Sieve.ofArrows.i h₁ = Sieve.ofArrows.i h₂
    · have hh : first ≫ Sieve.ofArrows.h h₁ = second ≫ Sieve.ofArrows.h h₂ := by
        apply (cancel_mono ((cofan U labels).inj (Sieve.ofArrows.i h₂))).mp
        simpa only [hidx] using hfac
      dsimp only [GrothendieckTopology.sheafifiedRepresentableCoconeFamily]
      simp only [← Functor.map_comp_apply, ← op_comp, hidx, hh]
    · have hbot : (⊥ : Sieve Z) ∈ J Z :=
        disjoint U labels hidx (first ≫ Sieve.ofArrows.h h₁) (second ≫ Sieve.ofArrows.h h₂) hfac
      apply (((isSheaf_iff_isSheaf_of_type J s.pt.obj).mp s.pt.property) _ hbot).isSeparatedFor.ext
      intro Y arrow impossible
      exact False.elim impossible
  let existing := J.isColimitSheafifiedRepresentableCofan.{u + 1, u + 1, u}
    (cofan U labels) (covering U labels) (disjoint U labels)
  let corrected : IsColimit
      (Cofan.mk (J.uliftSheafifiedRepresentable.{u + 1} (object U E))
        (fun i : E ↦ J.uliftSheafifiedRepresentableMap.{u + 1} (inclusion U labels i))) :=
    { existing with
      desc := fun s ↦
        (J.uliftSheafifiedRepresentableHomEquiv.{u + 1, u + 1, u} s.pt (object U E)).symm
          (((isSheaf_iff_isSheaf_of_type J s.pt.obj).mp s.pt.property) _ (covering U labels) |>.amalgamate
            (J.sheafifiedRepresentableCoconeFamily.{u + 1, u + 1, u} (cofan U labels) s)
            (hcompat s)) }
  exact (J.isColimitConstantSheafCofan.{u + 1, u + 1, u} Over.mkIdTerminal E).coconePointUniqueUpToIso
    corrected

/-- Pulling the inverse comparison back to a branch returns precisely its label. -/
theorem iso_inv_inclusion
    [HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] (e : E) :
    (X.smallEtaleTopology.over U).sheafifiedRepresentableMap (inclusion U labels e) ≫
      (iso U labels).inv =
        (GrothendieckTopology.constantSheafCofan.{u + 1, u + 1, u}
          (X.smallEtaleTopology.over U)
          (T := Over.mk (𝟙 U)) E).inj e := sorry

/-- A constant label maps to the associated evaluation branch of the product spectrum. -/
theorem iso_hom_inclusion
    [HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] (e : E) :
    (GrothendieckTopology.constantSheafCofan.{u + 1, u + 1, u}
          (X.smallEtaleTopology.over U)
        (T := Over.mk (𝟙 U)) E).inj e ≫ (iso U labels).hom =
      (X.smallEtaleTopology.over U).sheafifiedRepresentableMap (inclusion U labels e) := sorry

end AlgebraicGeometry.Scheme.Etale.ConstantFiniteRepresentation
