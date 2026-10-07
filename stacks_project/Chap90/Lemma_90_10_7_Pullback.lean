module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap90.Lemma_90_10_7_DualNumber

/-!
# Dual-number fibre products in `ArtinianLocalAlgCat`

The fibre product `A ×_k k[ε]` is the algebra pullback of `toResidue A` and
`dualNumberToResidue`, bundled as an object of `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable (A : ArtinianLocalAlgCat Λ k)

/-- The fibre product `A ×_k DualNumber k` is a local ring. -/
instance instIsLocalRing_dualNumberPullback :
    IsLocalRing (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) :=
  AlgHom.isLocalRing_pullback _ _

/-- The fibre product `A ×_k DualNumber k` is Artinian. -/
instance instIsArtinianRing_dualNumberPullback :
    IsArtinianRing (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) := sorry

/-- The first algebra projection of `A ×_k DualNumber k` is local. -/
instance instIsLocalHom_dualNumberPullbackFst :
    IsLocalHom (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom) := sorry

/-- The second algebra projection of `A ×_k DualNumber k` is local. -/
instance instIsLocalHom_dualNumberPullbackSnd :
    IsLocalHom (AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom) := sorry

/-- The canonical section `A → A × DualNumber k` of the first projection, sending `a` to
`(a, inl (toResidue a))`. -/
noncomputable def dualNumberPullbackSectionHom :
    A.carrier →ₐ[Λ] AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ A.carrier)
      (((inlAlgHom k k k).restrictScalars Λ).comp (toResidue A).hom))
    (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) sorry

/-- The canonical section of the first projection is a local homomorphism. -/
instance instIsLocalHom_dualNumberPullbackSectionHom :
    IsLocalHom (dualNumberPullbackSectionHom A) := sorry

/-- Residue-field identification of `A ×_k DualNumber k` with `k`, via the first projection
and the residue identification of `A`. -/
noncomputable def dualNumberPullbackResidueFieldIso :
    ResidueField (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    (A.residueFieldIso.toAlgHom.comp
      (ResidueField.mapAlgHom
        (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom)))
    ((ResidueField.mapAlgHom (dualNumberPullbackSectionHom A)).comp
      A.residueFieldIso.symm.toAlgHom)
    sorry sorry

/-- The fibre product `A ×_k DualNumber k`, viewed as an object of `ArtinianLocalAlgCat`. -/
noncomputable def dualNumberPullback : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom)
    (dualNumberPullbackResidueFieldIso A)

/-- The bundled dual-number fibre product has the algebra-pullback carrier. -/
theorem dualNumberPullback_carrier :
    (dualNumberPullback A).carrier =
      AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom := sorry

/-- The first projection `A ×_k DualNumber k ⟶ A`. -/
noncomputable def dualNumberPullbackFst : dualNumberPullback A ⟶ A where
  hom := AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The second projection `A ×_k DualNumber k ⟶ DualNumber k`. -/
noncomputable def dualNumberPullbackSnd : dualNumberPullback A ⟶ dualNumber Λ k where
  hom := AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The canonical section `A ⟶ A ×_k DualNumber k` of the first projection. -/
noncomputable def dualNumberPullbackSection : A ⟶ dualNumberPullback A where
  hom := dualNumberPullbackSectionHom A
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberPullbackFst` is the first algebra projection. -/
theorem dualNumberPullbackFst_hom :
    (dualNumberPullbackFst A).hom =
      AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom := sorry

/-- The underlying algebra map of `dualNumberPullbackSnd` is the second algebra projection. -/
theorem dualNumberPullbackSnd_hom :
    (dualNumberPullbackSnd A).hom =
      AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom := sorry

/-- The canonical section is a section of the first projection. -/
theorem dualNumberPullbackSection_comp_fst :
    dualNumberPullbackSection A ≫ dualNumberPullbackFst A = 𝟙 A := sorry

/-- The dual-number cospan square is a pullback in `ArtinianLocalAlgCat`. -/
theorem isPullback_dualNumberPullback :
    IsPullback (dualNumberPullbackFst A) (dualNumberPullbackSnd A)
      (toResidue A) (dualNumberToResidue Λ k) := sorry

end ArtinianLocalAlgCat
