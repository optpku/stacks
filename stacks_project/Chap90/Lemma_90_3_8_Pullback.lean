/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.RingTheory.LocalRing.ResidueField.Surjective
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Fibre products in `ArtinianLocalAlgCat`

The algebra fibre product of a cospan in `C_Λ` is local and Artinian. When a
leg is surjective, it carries a residue identification with `k` and therefore
is an object of `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

/-- The fibre product `A1 ×_A A2` is a local ring. -/
instance instIsLocalRing_pullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalRing (AlgHom.pullback f1.hom f2.hom) :=
  AlgHom.isLocalRing_pullback _ _

/-- The fibre product `A1 ×_A A2` is Artinian. -/
instance instIsArtinianRing_pullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsArtinianRing (AlgHom.pullback f1.hom f2.hom) := sorry

/-- The first algebra projection of `A1 ×_A A2` is local. -/
instance instIsLocalHom_pullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalHom (AlgHom.pullbackFst f1.hom f2.hom) := sorry

/-- The second algebra projection of `A1 ×_A A2` is local. -/
instance instIsLocalHom_pullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    IsLocalHom (AlgHom.pullbackSnd f1.hom f2.hom) := sorry

/-- Residue comparison of `A1 ×_A A2` with `k`, via the first projection and the
residue identification of `A1`. -/
noncomputable def pullbackResidueFieldHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) →ₐ[Λ] k :=
  A1.residueFieldIso.toAlgHom.comp
    (ResidueField.mapAlgHom (AlgHom.pullbackFst f1.hom f2.hom))

/-- The residue comparison of `A1 ×_A A2` sends the residue of a pair to the
residue identification of its first component. -/
theorem pullbackResidueFieldHom_apply (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (x : AlgHom.pullback f1.hom f2.hom) :
    pullbackResidueFieldHom f1 f2 (residue _ x) =
      A1.residueFieldIso (residue _ (AlgHom.pullbackFst f1.hom f2.hom x)) := sorry

/-- The residue comparison through the first projection agrees with the comparison
through the second projection. -/
theorem pullbackResidueFieldHom_eq_snd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    pullbackResidueFieldHom f1 f2 =
      A2.residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (AlgHom.pullbackSnd f1.hom f2.hom)) := sorry

/-- Residue identification of `A1 ×_A A2` with `k` via the first projection,
when the second leg is surjective. -/
noncomputable def pullbackResidueFieldIsoViaFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (hf2 : Function.Surjective f2.hom) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  (AlgEquiv.ofRingEquiv
      (f := RingHom.ResidueField.mapEquivOfSurjective
        (AlgHom.pullbackFst f1.hom f2.hom).toRingHom
        (AlgHom.surjective_pullbackFst_of_surjective f1.hom f2.hom hf2))
      (fun _ ↦ sorry)).trans
    A1.residueFieldIso

/-- Residue identification of `A1 ×_A A2` with `k` via the second projection,
when the first leg is surjective. -/
noncomputable def pullbackResidueFieldIsoViaSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (hf1 : Function.Surjective f1.hom) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  (AlgEquiv.ofRingEquiv
      (f := RingHom.ResidueField.mapEquivOfSurjective
        (AlgHom.pullbackSnd f1.hom f2.hom).toRingHom
        (AlgHom.surjective_pullbackSnd_of_surjective f1.hom f2.hom hf1))
      (fun _ ↦ sorry)).trans
    A2.residueFieldIso

/-- When the second leg is surjective, the first-projection residue
identification is the always-defined residue comparison. -/
theorem pullbackResidueFieldIsoViaFst_toAlgHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (hf2 : Function.Surjective f2.hom) :
    (pullbackResidueFieldIsoViaFst f1 f2 hf2).toAlgHom =
      pullbackResidueFieldHom f1 f2 := sorry

/-- When the first leg is surjective, the second-projection residue
identification is the second-leg residue comparison. -/
theorem pullbackResidueFieldIsoViaSnd_toAlgHom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (hf1 : Function.Surjective f1.hom) :
    (pullbackResidueFieldIsoViaSnd f1 f2 hf1).toAlgHom =
      A2.residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (AlgHom.pullbackSnd f1.hom f2.hom)) := sorry

/-- Residue-field identification of `A1 ×_A A2` with `k`, obtained from a
surjective projection and the residue identification of that source. -/
noncomputable def pullbackResidueFieldIso (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    ResidueField (AlgHom.pullback f1.hom f2.hom) ≃ₐ[Λ] k :=
  @dite _ (Function.Surjective f2.hom) (Classical.propDecidable _)
    (fun hf2 ↦ pullbackResidueFieldIsoViaFst f1 f2 hf2)
    (fun hf2 ↦ pullbackResidueFieldIsoViaSnd f1 f2 (h.resolve_right hf2))

/-- When the second leg is surjective, the residue identification of the fibre
product is the comparison through the first projection. -/
theorem pullbackResidueFieldIso_toAlgHom_of_surjective_snd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (hf2 : Function.Surjective f2.hom) :
    (pullbackResidueFieldIso f1 f2 (Or.inr hf2)).toAlgHom =
      pullbackResidueFieldHom f1 f2 := sorry

/-- The fibre product `A1 ×_A A2`, viewed as an object of `ArtinianLocalAlgCat`,
when a leg is surjective. -/
noncomputable def pullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f1.hom f2.hom) (pullbackResidueFieldIso f1 f2 h)

/-- The bundled fibre product has the algebra-pullback carrier. -/
theorem pullback_carrier (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    (pullback f1 f2 h).carrier = AlgHom.pullback f1.hom f2.hom := sorry

/-- The first projection `A1 ×_A A2 ⟶ A1`. -/
noncomputable def pullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    pullback f1 f2 h ⟶ A1 where
  hom := AlgHom.pullbackFst f1.hom f2.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The second projection `A1 ×_A A2 ⟶ A2`. -/
noncomputable def pullbackSnd (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    pullback f1 f2 h ⟶ A2 where
  hom := AlgHom.pullbackSnd f1.hom f2.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `pullbackFst` is the first algebra projection. -/
theorem pullbackFst_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    (pullbackFst f1 f2 h).hom = AlgHom.pullbackFst f1.hom f2.hom := sorry

/-- The underlying algebra map of `pullbackSnd` is the second algebra projection. -/
theorem pullbackSnd_hom (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    (pullbackSnd f1 f2 h).hom = AlgHom.pullbackSnd f1.hom f2.hom := sorry

/-- The cospan square of a fibre product with a surjective leg is a pullback in
`ArtinianLocalAlgCat`. -/
theorem isPullback_pullback (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective f1.hom ∨ Function.Surjective f2.hom) :
    IsPullback (pullbackFst f1 f2 h) (pullbackSnd f1 f2 h) f1 f2 := sorry

/-- The fibre product `A1 ×_A A2`, viewed as an object of `ArtinianLocalAlgCat`,
when the canonical residue comparison is surjective. -/
noncomputable def pullbackOfResidueSurjective (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective (pullbackResidueFieldHom f1 f2)) :
    ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f1.hom f2.hom)
    (AlgEquiv.ofBijective (pullbackResidueFieldHom f1 f2)
      ⟨RingHom.injective (pullbackResidueFieldHom f1 f2).toRingHom, h⟩)

/-- The residue-surjective fibre product has the algebra-pullback carrier and the
canonical residue comparison as its residue identification. -/
theorem pullbackOfResidueSurjective_spec (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : Function.Surjective (pullbackResidueFieldHom f1 f2)) :
    (pullbackOfResidueSurjective f1 f2 h).carrier = AlgHom.pullback f1.hom f2.hom ∧
      (pullbackOfResidueSurjective f1 f2 h).residueFieldIso.toAlgHom =
        pullbackResidueFieldHom f1 f2 := sorry

end ArtinianLocalAlgCat

