/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances

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

/-- The pullback residue field is identified with `k` through its first projection. -/
noncomputable def cospanPullbackResidueFieldIso (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    (A1.residueFieldIso.toAlgHom.comp
      (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom)))
    ((ResidueField.mapAlgHom (cospanPullbackSectionHom f1 f2 h hh)).comp
      A1.residueFieldIso.symm.toAlgHom)
    sorry sorry

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

/-- The section is a morphism into the bundled pullback. -/
noncomputable def cospanPullbackSection (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : A1 ⟶ cospanPullback f1 f2 h hh :=
  Hom.of (cospanPullbackSectionHom f1 f2 h hh)
    (instIsLocalHom_cospanPullbackSectionHom f1 f2 h hh)
    sorry

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

end ArtinianLocalAlgCat
