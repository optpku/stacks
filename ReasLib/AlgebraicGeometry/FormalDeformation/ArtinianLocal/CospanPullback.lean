/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension
public import ReasLib.RingTheory.LocalRing.Length.ResidueImage
public import ReasLib.RingTheory.LocalRing.ResidueField.Surjective
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Henselian

/-!
# Fibre products of cospans in `ArtinianLocalAlgCat`

The fibre product of a cospan of residue-identified Artinian local algebras is
the algebra pullback of its underlying maps, with the induced residue-field
identification.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

/-- The pullback of a local algebra map has a local carrier. -/
instance instIsLocalRing_cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalRing (AlgHom.pullback f1.hom f2.hom) :=
  @AlgHom.isLocalRing_pullback _ _ _ _ _ _ _ _ _ _ _ _ f1.hom f2.hom f2.isLocalHom

/-- The algebra pullback is Artinian. -/
instance instIsArtinianRing_cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsArtinianRing (AlgHom.pullback f1.hom f2.hom) := sorry

/-- The first algebra projection is local. -/
instance instIsLocalHom_cospanPullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalHom (AlgHom.pullbackFst f1.hom f2.hom) := by
  let h : IsLocalHom (f1.hom.toRingHom.pullbackFst f2.hom.toRingHom) :=
    @RingHom.isLocalHom_pullbackFst _ _ _ _ _ _ f1.hom.toRingHom f2.hom.toRingHom
      ⟨fun x hx => f2.isLocalHom.map_nonunit x hx⟩
  exact ⟨fun x hx => h.map_nonunit x hx⟩

/-- The second algebra projection is local. -/
instance instIsLocalHom_cospanPullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalHom (AlgHom.pullbackSnd f1.hom f2.hom) := by
  let h : IsLocalHom (f1.hom.toRingHom.pullbackSnd f2.hom.toRingHom) :=
    @RingHom.isLocalHom_pullbackSnd _ _ _ _ _ _ f1.hom.toRingHom f2.hom.toRingHom
      ⟨fun x hx => f1.isLocalHom.map_nonunit x hx⟩
  exact ⟨fun x hx => h.map_nonunit x hx⟩

/-- The section algebra map has image in the pullback. -/
theorem cospanPullbackSectionHom_mem (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (u : A1.carrier) :
    (AlgHom.prod (AlgHom.id Λ A1.carrier) h.hom u) ∈
      AlgHom.pullback f1.hom f2.hom := sorry

/-- The section algebra map sends `u` to `(u, h(u))`. -/
noncomputable def cospanPullbackSectionHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    A1.carrier →ₐ[Λ] AlgHom.pullback f1.hom f2.hom :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ A1.carrier) h.hom)
    (AlgHom.pullback f1.hom f2.hom)
    (cospanPullbackSectionHom_mem f1 f2 h hh)

/-- The section algebra map is local. -/
theorem cospanPullbackSectionHom_isLocalHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    IsLocalHom (cospanPullbackSectionHom f1 f2 h hh) := sorry

/-- The section algebra map is local as a ring homomorphism. -/
instance instIsLocalHom_cospanPullbackSectionHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    IsLocalHom (cospanPullbackSectionHom f1 f2 h hh) :=
  cospanPullbackSectionHom_isLocalHom f1 f2 h hh

/-- The first residue-field map is inverse to the section-induced map. -/
theorem cospanPullbackResidueFieldIso_left_inv (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    Function.LeftInverse
      (A1.residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom)))
      ((ResidueField.mapAlgHom (cospanPullbackSectionHom f1 f2 h hh)).comp
        A1.residueFieldIso.symm.toAlgHom) := sorry

/-- The section-induced residue-field map is inverse to the first projection map. -/
theorem cospanPullbackResidueFieldIso_right_inv (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    Function.RightInverse
      (A1.residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom)))
      ((ResidueField.mapAlgHom (cospanPullbackSectionHom f1 f2 h hh)).comp
        A1.residueFieldIso.symm.toAlgHom) := sorry

/-- The pullback residue field is identified with `k` through its first projection. -/
noncomputable def cospanPullbackResidueFieldIso (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    (A1.residueFieldIso.toAlgHom.comp
      (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom)))
    ((ResidueField.mapAlgHom (cospanPullbackSectionHom f1 f2 h hh)).comp
      A1.residueFieldIso.symm.toAlgHom)
    (AlgHom.ext (cospanPullbackResidueFieldIso_left_inv f1 f2 h hh))
    (AlgHom.ext (cospanPullbackResidueFieldIso_right_inv f1 f2 h hh))

/-- The cospan pullback is bundled as an Artinian local algebra. -/
noncomputable def cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f1.hom f2.hom) (cospanPullbackResidueFieldIso f1 f2 h hh)

/-- The bundled cospan pullback has the algebra-pullback carrier. -/
theorem cospanPullback_carrier (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullback f1 f2 h hh).carrier = CommRingCat.of (AlgHom.pullback f1.hom f2.hom) := sorry

/-- Residue compatibility for the first projection. -/
theorem cospanPullbackFst_residue_compat (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    residueCompat (AlgHom.pullbackFst f1.hom f2.hom)
      (instIsLocalHom_cospanPullbackFst f1 f2) =
      residueIsoHom (cospanPullback f1 f2 h hh) := sorry

/-- Residue compatibility for the second projection. -/
theorem cospanPullbackSnd_residue_compat (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    residueCompat (AlgHom.pullbackSnd f1.hom f2.hom)
      (instIsLocalHom_cospanPullbackSnd f1 f2) =
      residueIsoHom (cospanPullback f1 f2 h hh) := sorry

/-- The first projection of the bundled cospan pullback. -/
noncomputable def cospanPullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : cospanPullback f1 f2 h hh ⟶ A1 :=
  Hom.of (AlgHom.pullbackFst f1.hom f2.hom)
    (instIsLocalHom_cospanPullbackFst f1 f2)
    (cospanPullbackFst_residue_compat f1 f2 h hh)

/-- The second projection of the bundled cospan pullback. -/
noncomputable def cospanPullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : cospanPullback f1 f2 h hh ⟶ A2 :=
  Hom.of (AlgHom.pullbackSnd f1.hom f2.hom)
    (instIsLocalHom_cospanPullbackSnd f1 f2)
    (cospanPullbackSnd_residue_compat f1 f2 h hh)

/-- The canonical section preserves the chosen residue identifications. -/
theorem cospanPullbackSection_residue_compat (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    residueCompat (B := cospanPullback f1 f2 h hh) (cospanPullbackSectionHom f1 f2 h hh)
      (instIsLocalHom_cospanPullbackSectionHom f1 f2 h hh) = residueIsoHom A1 := sorry

/-- The section is a morphism into the bundled pullback. -/
noncomputable def cospanPullbackSection (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : A1 ⟶ cospanPullback f1 f2 h hh :=
  Hom.of (cospanPullbackSectionHom f1 f2 h hh)
    (instIsLocalHom_cospanPullbackSectionHom f1 f2 h hh)
    (cospanPullbackSection_residue_compat f1 f2 h hh)

/-- The lift algebra map has image in the pullback. -/
theorem cospanPullbackLiftHom_mem {B : ArtinianLocalAlgCat Λ k}
  (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) (z : B.carrier) :
    (AlgHom.prod g₁.hom g₂.hom z) ∈ AlgHom.pullback f1.hom f2.hom := sorry

/-- The underlying algebra map induced by two compatible cospan legs. -/
noncomputable def cospanPullbackLiftHom {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    B.carrier →ₐ[Λ] (cospanPullback f1 f2 h hh).carrier :=
  AlgHom.codRestrict (AlgHom.prod g₁.hom g₂.hom) (AlgHom.pullback f1.hom f2.hom)
    (cospanPullbackLiftHom_mem f1 f2 h hh g₁ g₂ hg)

/-- The algebra map induced by compatible cospan legs is local. -/
theorem cospanPullbackLiftHom_isLocalHom {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    IsLocalHom (cospanPullbackLiftHom f1 f2 h hh g₁ g₂ hg) := sorry

/-- The induced lift algebra map has a reusable localness instance. -/
instance instIsLocalHom_cospanPullbackLiftHom {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    IsLocalHom (cospanPullbackLiftHom f1 f2 h hh g₁ g₂ hg) :=
  cospanPullbackLiftHom_isLocalHom f1 f2 h hh g₁ g₂ hg

/-- The induced lift algebra map preserves the chosen residue identifications. -/
theorem cospanPullbackLiftHom_residue_compat {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    residueCompat (cospanPullbackLiftHom f1 f2 h hh g₁ g₂ hg)
      (instIsLocalHom_cospanPullbackLiftHom f1 f2 h hh g₁ g₂ hg) =
      residueIsoHom B := sorry

/-- The induced map into the cospan pullback. -/
noncomputable def cospanPullbackLift {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    B ⟶ cospanPullback f1 f2 h hh :=
  Hom.of (cospanPullbackLiftHom f1 f2 h hh g₁ g₂ hg)
    (instIsLocalHom_cospanPullbackLiftHom f1 f2 h hh g₁ g₂ hg)
    (cospanPullbackLiftHom_residue_compat f1 f2 h hh g₁ g₂ hg)

/-- The underlying algebra map of the first cospan-pullback projection. -/
theorem cospanPullbackFst_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackFst f1 f2 h hh).hom = AlgHom.pullbackFst f1.hom f2.hom := rfl

/-- The underlying algebra map of the second cospan-pullback projection. -/
theorem cospanPullbackSnd_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackSnd f1 f2 h hh).hom = AlgHom.pullbackSnd f1.hom f2.hom := rfl

/-- The two cospan-pullback projections agree after mapping to the base. -/
theorem cospanPullbackFst_comp_eq_snd_comp (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullbackFst f1 f2 h hh ≫ f1 = cospanPullbackSnd f1 f2 h hh ≫ f2 := sorry

/-- The canonical section is a section of the first projection. -/
theorem cospanPullbackSection_comp_fst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullbackSection f1 f2 h hh ≫ cospanPullbackFst f1 f2 h hh = 𝟙 A1 := sorry

/-- The cospan-pullback lift projects to its first prescribed map. -/
theorem cospanPullbackLift_comp_fst {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    cospanPullbackLift f1 f2 h hh g₁ g₂ hg ≫ cospanPullbackFst f1 f2 h hh = g₁ := sorry

/-- The cospan-pullback lift projects to its second prescribed map. -/
theorem cospanPullbackLift_comp_snd {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    cospanPullbackLift f1 f2 h hh g₁ g₂ hg ≫ cospanPullbackSnd f1 f2 h hh = g₂ := sorry

/-- The cospan-pullback square satisfies the categorical universal property. -/
theorem isPullback_cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    IsPullback (cospanPullbackFst f1 f2 h hh) (cospanPullbackSnd f1 f2 h hh) f1 f2 := sorry

/-- The residue comparison of an algebra pullback with `k` through its first projection. -/
noncomputable def pullbackResidueFieldHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) →ₐ[Λ] k :=
  A1.residueFieldIso.toAlgHom.comp
    (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom))

/-- The residue comparison sends the residue of a pair to that of its first component. -/
theorem pullbackResidueFieldHom_apply (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (x : AlgHom.pullback f1.hom f2.hom) :
    pullbackResidueFieldHom f1 f2 (residue _ x) =
      A1.residueFieldIso (residue _ (AlgHom.pullbackFst f1.hom f2.hom x)) := rfl

private theorem residueFieldIso_hom_apply (f : A1 ⟶ A) (x : A1.carrier) :
    A.residueFieldIso (residue _ (f.hom x)) = A1.residueFieldIso (residue _ x) :=
  DFunLike.congr_fun (Hom.residue_compat f) (residue _ x)

/-- The residue comparisons through the two projections agree. -/
theorem pullbackResidueFieldHom_eq_snd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    pullbackResidueFieldHom f1 f2 =
      A2.residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (AlgHom.pullbackSnd f1.hom f2.hom)) := by
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  change A1.residueFieldIso (residue _ x.1.1) = A2.residueFieldIso (residue _ x.1.2)
  calc
    _ = A.residueFieldIso (residue _ (f1.hom x.1.1)) :=
      (residueFieldIso_hom_apply f1 _).symm
    _ = A.residueFieldIso (residue _ (f2.hom x.1.2)) :=
      congrArg (fun a => A.residueFieldIso (residue _ a)) x.2
    _ = _ := residueFieldIso_hom_apply f2 _

/-- A surjective leg makes the canonical pullback residue comparison surjective. -/
theorem surjective_pullbackResidueFieldHom_of_surjective (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    Function.Surjective (pullbackResidueFieldHom f1 f2) := by
  rcases h with h | h
  · letI : IsLocalHom (AlgHom.pullbackSnd f1.hom f2.hom).toRingHom :=
      ⟨fun x hx => (instIsLocalHom_cospanPullbackSnd f1 f2).map_nonunit x hx⟩
    rw [pullbackResidueFieldHom_eq_snd]
    exact A2.residueFieldIso.surjective.comp
      (RingHom.ResidueField.map_bijective_of_surjective
        (AlgHom.pullbackSnd f1.hom f2.hom).toRingHom
        (AlgHom.surjective_pullbackSnd_of_surjective f1.hom f2.hom h)).2
  · letI : IsLocalHom (AlgHom.pullbackFst f1.hom f2.hom).toRingHom :=
      ⟨fun x hx => (instIsLocalHom_cospanPullbackFst f1 f2).map_nonunit x hx⟩
    exact A1.residueFieldIso.surjective.comp
      (RingHom.ResidueField.map_bijective_of_surjective
        (AlgHom.pullbackFst f1.hom f2.hom).toRingHom
        (AlgHom.surjective_pullbackFst_of_surjective f1.hom f2.hom h)).2

/-- A pullback with a surjective leg has its residue field canonically identified with `k`. -/
noncomputable def pullbackResidueFieldIso (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofBijective (pullbackResidueFieldHom f1 f2)
    ⟨RingHom.injective (pullbackResidueFieldHom f1 f2).toRingHom,
      surjective_pullbackResidueFieldHom_of_surjective f1 f2 h⟩

/-- The residue equivalence for a surjective leg has the canonical comparison as forward map. -/
theorem pullbackResidueFieldIso_toAlgHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    (pullbackResidueFieldIso f1 f2 h).toAlgHom = pullbackResidueFieldHom f1 f2 := rfl

/-- The algebra pullback with a surjective leg is a residue-identified Artinian local algebra. -/
noncomputable def pullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f1.hom f2.hom) (pullbackResidueFieldIso f1 f2 h)

/-- The bundled pullback has the concrete algebra-pullback carrier. -/
theorem pullback_carrier (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    ((pullback f1 f2 h).carrier : Type u) = AlgHom.pullback f1.hom f2.hom := sorry

/-- The first projection preserves the chosen residue identifications. -/
theorem pullbackFst_residue_compat (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    residueCompat (AlgHom.pullbackFst f1.hom f2.hom)
      (instIsLocalHom_cospanPullbackFst f1 f2) = residueIsoHom (pullback f1 f2 h) := sorry

/-- The second projection preserves the chosen residue identifications. -/
theorem pullbackSnd_residue_compat (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    residueCompat (AlgHom.pullbackSnd f1.hom f2.hom)
      (instIsLocalHom_cospanPullbackSnd f1 f2) = residueIsoHom (pullback f1 f2 h) := sorry

/-- The first projection of the bundled pullback. -/
noncomputable def pullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    pullback f1 f2 h ⟶ A1 :=
  Hom.of (AlgHom.pullbackFst f1.hom f2.hom) (instIsLocalHom_cospanPullbackFst f1 f2)
    (pullbackFst_residue_compat f1 f2 h)

/-- The second projection of the bundled pullback. -/
noncomputable def pullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    pullback f1 f2 h ⟶ A2 :=
  Hom.of (AlgHom.pullbackSnd f1.hom f2.hom) (instIsLocalHom_cospanPullbackSnd f1 f2)
    (pullbackSnd_residue_compat f1 f2 h)

/-- The underlying algebra map of the first projection is the algebra-pullback projection. -/
theorem pullbackFst_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    (pullbackFst f1 f2 h).hom = AlgHom.pullbackFst f1.hom f2.hom := sorry

/-- The underlying algebra map of the second projection is the algebra-pullback projection. -/
theorem pullbackSnd_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    (pullbackSnd f1 f2 h).hom = AlgHom.pullbackSnd f1.hom f2.hom := sorry

/-- A pullback with a surjective leg satisfies the categorical universal property. -/
theorem isPullback_pullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    IsPullback (pullbackFst f1 f2 h) (pullbackSnd f1 f2 h) f1 f2 := sorry

/-- A residue-surjective algebra pullback is a residue-identified Artinian local algebra. -/
noncomputable def pullbackOfResidueSurjective (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective (pullbackResidueFieldHom f1 f2)) : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f1.hom f2.hom)
    (AlgEquiv.ofBijective (pullbackResidueFieldHom f1 f2)
      ⟨RingHom.injective (pullbackResidueFieldHom f1 f2).toRingHom, h⟩)

/-- A residue-surjective pullback has the concrete carrier and canonical residue comparison. -/
theorem pullbackOfResidueSurjective_spec (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective (pullbackResidueFieldHom f1 f2)) :
    ((pullbackOfResidueSurjective f1 f2 h).carrier : Type u) = AlgHom.pullback f1.hom f2.hom ∧
      (pullbackOfResidueSurjective f1 f2 h).residueFieldIso.toAlgHom =
        pullbackResidueFieldHom f1 f2 := sorry

/-- Pulling back a small second leg gives a small first projection. -/
instance instIsSmallExtension_pullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [IsSmallExtension f2] :
    IsSmallExtension (pullbackFst f1 f2 (Or.inr IsSmallExtension.surjective)) := sorry

private theorem exists_root_with_residue (B : ArtinianLocalAlgCat Λ k)
    (p : Polynomial Λ) (hp : p.Monic) (x : k)
    (hx : Polynomial.aeval x p = 0) (hx' : Polynomial.aeval x p.derivative ≠ 0) :
    ∃ b : B.carrier, Polynomial.aeval b p = 0 ∧
      B.residueFieldIso (residue _ b) = x := by
  letI : HenselianLocalRing B.carrier :=
    { toIsLocalRing := inferInstance
      is_henselian := fun f hf a₀ h₀ h' =>
        HenselianRing.is_henselian f hf a₀ h₀ (h'.map (residue B.carrier)) }
  let r : B.carrier →ₐ[Λ] k :=
    B.residueFieldIso.toAlgHom.comp (Ideal.Quotient.mkₐ Λ (IsLocalRing.maximalIdeal B.carrier))
  have hr : Function.Surjective r := B.residueFieldIso.surjective.comp residue_surjective
  obtain ⟨b, hb, hbx⟩ := ((HenselianLocalRing.TFAE B.carrier).out 0 2 rfl rfl).mp
    (inferInstance : HenselianLocalRing B.carrier)
    r.toRingHom hr (p.map (algebraMap Λ B.carrier)) (hp.map _) x
    (by simpa [Polynomial.eval₂_map, Polynomial.aeval_def] using hx)
    (by simpa [Polynomial.derivative_map, Polynomial.eval₂_map, Polynomial.aeval_def] using hx')
  exact ⟨b, by simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hb, hbx⟩

/-- Separability over the base image makes the canonical pullback residue comparison surjective. -/
theorem surjective_pullbackResidueFieldHom_of_separable (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    Function.Surjective (pullbackResidueFieldHom f1 f2) := by
  intro x
  have hs := Algebra.IsSeparable.isSeparable (Algebra.residueImage Λ k) x
  obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective
      (f := algebraMap Λ (Algebra.residueImage Λ k))
      Ideal.Quotient.mk_surjective (minpoly (Algebra.residueImage Λ k) x))
    (minpoly.monic hs.isIntegral)
  have heval (q : Polynomial Λ) : Polynomial.aeval x q =
      Polynomial.aeval x (q.map (algebraMap Λ (Algebra.residueImage Λ k))) :=
    Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq Λ (Algebra.residueImage Λ k) k)
      q x
  have hx : Polynomial.aeval x p = 0 := by
    rw [heval, hp, minpoly.aeval]
  have hx' : Polynomial.aeval x p.derivative ≠ 0 := by
    rw [heval, ← Polynomial.derivative_map, hp]
    exact hs.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨b₁, hb₁, hx₁⟩ := exists_root_with_residue A1 p hpm x hx hx'
  obtain ⟨b₂, hb₂, hx₂⟩ := exists_root_with_residue A2 p hpm x hx hx'
  have hres₁ : A.residueFieldIso (residue _ (f1.hom b₁)) = x :=
    (residueFieldIso_hom_apply f1 b₁).trans hx₁
  have hres₂ : A.residueFieldIso (residue _ (f2.hom b₂)) = x :=
    (residueFieldIso_hom_apply f2 b₂).trans hx₂
  have hroot₁ : Polynomial.aeval (f1.hom b₁) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hb₁, map_zero]
  have hroot₂ : Polynomial.aeval (f2.hom b₂) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hb₂, map_zero]
  have heq : f1.hom b₁ = f2.hom b₂ := by
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := p.map (algebraMap Λ A.carrier))
    · simpa [Polynomial.eval_map_algebraMap] using hroot₁
    · simpa [Polynomial.eval_map_algebraMap] using hroot₂
    · change (f1.hom b₁ - f2.hom b₂) ∈ IsLocalRing.maximalIdeal A.carrier
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact A.residueFieldIso.injective (hres₁.trans hres₂.symm)
    · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap,
        ← residue_ne_zero_iff_isUnit]
      intro hzero
      let r : A.carrier →ₐ[Λ] k :=
        A.residueFieldIso.toAlgHom.comp (Ideal.Quotient.mkₐ Λ (IsLocalRing.maximalIdeal A.carrier))
      have hz : r (Polynomial.aeval (f1.hom b₁) p.derivative) = 0 := by
        change A.residueFieldIso (residue _ (Polynomial.aeval (f1.hom b₁) p.derivative)) = 0
        exact (congrArg A.residueFieldIso hzero).trans (map_zero _)
      rw [← Polynomial.aeval_algHom_apply, show r (f1.hom b₁) = x from hres₁] at hz
      exact hx' hz
  exact ⟨residue _ (⟨(b₁, b₂), heq⟩ : AlgHom.pullback f1.hom f2.hom), hx₁⟩

/-- The pullback over a separable residue extension is a residue-identified Artinian local algebra. -/
noncomputable def pullbackOfSeparable (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] : ArtinianLocalAlgCat Λ k :=
  pullbackOfResidueSurjective f1 f2 (surjective_pullbackResidueFieldHom_of_separable f1 f2)

/-- The separable pullback has the concrete carrier and canonical residue comparison. -/
theorem pullbackOfSeparable_spec (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ((pullbackOfSeparable f1 f2).carrier : Type u) = AlgHom.pullback f1.hom f2.hom ∧
      (pullbackOfSeparable f1 f2).residueFieldIso.toAlgHom =
        pullbackResidueFieldHom f1 f2 := sorry

end ArtinianLocalAlgCat
