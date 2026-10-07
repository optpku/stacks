module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Fibre products of cospans in `ArtinianLocalAlgCat`

The fibre product `A1 ×_A A2` of a cospan `A1 ⟶ A ⟵ A2` is the algebra pullback of
the underlying maps, bundled as an object of `C_Λ` using the source section
`h : A1 ⟶ A2` of `f2`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

/-- The fibre product `A1 ×_A A2` is a local ring. -/
instance instIsLocalRing_cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalRing (AlgHom.pullback f1.hom f2.hom) :=
  AlgHom.isLocalRing_pullback _ _

/-- The fibre product `A1 ×_A A2` is Artinian. -/
instance instIsArtinianRing_cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsArtinianRing (AlgHom.pullback f1.hom f2.hom) := sorry

/-- The first algebra projection of `A1 ×_A A2` is local. -/
instance instIsLocalHom_cospanPullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalHom (AlgHom.pullbackFst f1.hom f2.hom) := sorry

/-- The second algebra projection of `A1 ×_A A2` is local. -/
instance instIsLocalHom_cospanPullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalHom (AlgHom.pullbackSnd f1.hom f2.hom) := sorry

/-- The algebra map `A1 → A1 ×_A A2` sending `u` to `(u, h(u))`. -/
noncomputable def cospanPullbackSectionHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    A1.carrier →ₐ[Λ] AlgHom.pullback f1.hom f2.hom :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ A1.carrier) h.hom)
    (AlgHom.pullback f1.hom f2.hom) sorry

/-- The section `u ↦ (u, h(u))` is a local homomorphism. -/
instance instIsLocalHom_cospanPullbackSectionHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    IsLocalHom (cospanPullbackSectionHom f1 f2 h hh) := sorry

/-- Residue-field identification of `A1 ×_A A2` with `k`, via the first projection
and the residue identification of `A1`. -/
noncomputable def cospanPullbackResidueFieldIso (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    (A1.residueFieldIso.toAlgHom.comp
      (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom)))
    ((ResidueField.mapAlgHom (cospanPullbackSectionHom f1 f2 h hh)).comp
      A1.residueFieldIso.symm.toAlgHom)
    sorry sorry

/-- The fibre product `A1 ×_A A2`, viewed as an object of `ArtinianLocalAlgCat`. -/
noncomputable def cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f1.hom f2.hom) (cospanPullbackResidueFieldIso f1 f2 h hh)

/-- The bundled cospan fibre product has the algebra-pullback carrier. -/
theorem cospanPullback_carrier (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullback f1 f2 h hh).carrier = AlgHom.pullback f1.hom f2.hom := sorry

/-- The first projection `A1 ×_A A2 ⟶ A1`. -/
noncomputable def cospanPullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : cospanPullback f1 f2 h hh ⟶ A1 where
  hom := AlgHom.pullbackFst f1.hom f2.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The second projection `A1 ×_A A2 ⟶ A2`. -/
noncomputable def cospanPullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : cospanPullback f1 f2 h hh ⟶ A2 where
  hom := AlgHom.pullbackSnd f1.hom f2.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The composite `A1 ×_A A2 ⟶ A` of the first projection with `f1`. -/
noncomputable def cospanPullbackToBase (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : cospanPullback f1 f2 h hh ⟶ A :=
  cospanPullbackFst f1 f2 h hh ≫ f1

/-- The section `A1 ⟶ A1 ×_A A2` of the first projection, sending `u` to `(u, h(u))`. -/
noncomputable def cospanPullbackSection (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) : A1 ⟶ cospanPullback f1 f2 h hh where
  hom := cospanPullbackSectionHom f1 f2 h hh
  isLocalHom := sorry
  residue_compat := sorry

/-- The induced map into `A1 ×_A A2` from a pair of maps that agree after `f1` and `f2`. -/
noncomputable def cospanPullbackLift {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    B ⟶ cospanPullback f1 f2 h hh where
  hom :=
    AlgHom.codRestrict (AlgHom.prod g₁.hom g₂.hom) (AlgHom.pullback f1.hom f2.hom) sorry
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `cospanPullbackFst` is the first algebra projection. -/
theorem cospanPullbackFst_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackFst f1 f2 h hh).hom = AlgHom.pullbackFst f1.hom f2.hom := sorry

/-- The underlying algebra map of `cospanPullbackSnd` is the second algebra projection. -/
theorem cospanPullbackSnd_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackSnd f1 f2 h hh).hom = AlgHom.pullbackSnd f1.hom f2.hom := sorry

/-- The map to the base is the first projection followed by `f1`. -/
theorem cospanPullbackToBase_eq (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullbackToBase f1 f2 h hh = cospanPullbackFst f1 f2 h hh ≫ f1 := sorry

/-- The two projections of `A1 ×_A A2` agree after composing to `A`. -/
theorem cospanPullbackFst_comp_eq_Snd_comp (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullbackFst f1 f2 h hh ≫ f1 = cospanPullbackSnd f1 f2 h hh ≫ f2 := sorry

/-- The section is a section of the first projection. -/
theorem cospanPullbackSection_comp_fst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullbackSection f1 f2 h hh ≫ cospanPullbackFst f1 f2 h hh = 𝟙 A1 := sorry

/-- The induced lift projects to the first given map. -/
theorem cospanPullbackLift_comp_fst {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    cospanPullbackLift f1 f2 h hh g₁ g₂ hg ≫ cospanPullbackFst f1 f2 h hh = g₁ := sorry

/-- The induced lift projects to the second given map. -/
theorem cospanPullbackLift_comp_snd {B : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (h : A1 ⟶ A2) (hh : h ≫ f2 = f1)
    (g₁ : B ⟶ A1) (g₂ : B ⟶ A2) (hg : g₁ ≫ f1 = g₂ ≫ f2) :
    cospanPullbackLift f1 f2 h hh g₁ g₂ hg ≫ cospanPullbackSnd f1 f2 h hh = g₂ := sorry

/-- The cospan square is a pullback in `ArtinianLocalAlgCat`. -/
theorem isPullback_cospanPullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    IsPullback (cospanPullbackFst f1 f2 h hh) (cospanPullbackSnd f1 f2 h hh) f1 f2 :=
  sorry

/-- The cospan fibre product is a pullback cone for `f1, f2`, and its map to the base is
the composite of the first projection with `f1`. -/
theorem cospanPullback_spec (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    IsPullback (cospanPullbackFst f1 f2 h hh) (cospanPullbackSnd f1 f2 h hh) f1 f2 ∧
      cospanPullbackToBase f1 f2 h hh = cospanPullbackFst f1 f2 h hh ≫ f1 := sorry

end ArtinianLocalAlgCat
