module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZero

/-!
# Square-zero fibre products in `ArtinianLocalAlgCat`

The fibre product `A ×_k k[I]` is the algebra pullback of `toResidue A` and
`squareZeroToResidue Λ k I`, bundled as an object of `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable (A : ArtinianLocalAlgCat Λ k)
variable (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I]

/-- The fibre product `A ×_k TrivSqZeroExt k I` is a local ring. -/
instance instIsLocalRing_squareZeroPullback :
    IsLocalRing (AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom) :=
  @AlgHom.isLocalRing_pullback _ _ _ _ _ _ _ _ _ _ _ _
    (toResidue A).hom (squareZeroToResidue Λ k I).hom (squareZeroToResidue Λ k I).isLocalHom

/-- The fibre product `A ×_k TrivSqZeroExt k I` is Artinian. -/
instance instIsArtinianRing_squareZeroPullback :
    IsArtinianRing (AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom) := sorry

/-- The first algebra projection of `A ×_k TrivSqZeroExt k I` is local. -/
instance instIsLocalHom_squareZeroPullbackFst :
    IsLocalHom (AlgHom.pullbackFst (toResidue A).hom (squareZeroToResidue Λ k I).hom) := sorry

/-- The second algebra projection of `A ×_k TrivSqZeroExt k I` is local. -/
instance instIsLocalHom_squareZeroPullbackSnd :
    IsLocalHom (AlgHom.pullbackSnd (toResidue A).hom (squareZeroToResidue Λ k I).hom) := sorry

/-- The canonical section `A → A × TrivSqZeroExt k I` of the first projection, sending `a` to
`(a, inl (toResidue a))`. -/
noncomputable def squareZeroPullbackSectionHom :
    A.carrier →ₐ[Λ] AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ A.carrier)
      (((inlAlgHom k k I).restrictScalars Λ).comp (toResidue A).hom))
    (AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom) sorry

/-- The canonical section of the first projection is a local homomorphism. -/
instance instIsLocalHom_squareZeroPullbackSectionHom :
    IsLocalHom (squareZeroPullbackSectionHom A I) := sorry

/-- Residue-field identification of `A ×_k TrivSqZeroExt k I` with `k`, via the first
projection and the residue identification of `A`. -/
noncomputable def squareZeroPullbackResidueFieldIso :
    ResidueField (AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    (A.residueFieldIso.toAlgHom.comp
      (ResidueField.mapAlgHom
        (AlgHom.pullbackFst (toResidue A).hom (squareZeroToResidue Λ k I).hom)))
    ((ResidueField.mapAlgHom (squareZeroPullbackSectionHom A I)).comp
      A.residueFieldIso.symm.toAlgHom)
    sorry sorry

/-- The fibre product `A ×_k TrivSqZeroExt k I`, viewed as an object of
`ArtinianLocalAlgCat`. -/
noncomputable def squareZeroPullback : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom)
    (squareZeroPullbackResidueFieldIso A I)

/-- The bundled square-zero fibre product has the algebra-pullback carrier. -/
theorem squareZeroPullback_carrier :
    (squareZeroPullback A I).carrier =
      (AlgHom.pullback (toResidue A).hom (squareZeroToResidue Λ k I).hom : Type u) := sorry

/-- The first projection `A ×_k k[I] ⟶ A`. -/
noncomputable def squareZeroPullbackFst : squareZeroPullback A I ⟶ A :=
  Hom.of (AlgHom.pullbackFst (toResidue A).hom (squareZeroToResidue Λ k I).hom)
    (instIsLocalHom_squareZeroPullbackFst A I) sorry

/-- The second projection `A ×_k k[I] ⟶ k[I]`. -/
noncomputable def squareZeroPullbackSnd : squareZeroPullback A I ⟶ squareZero Λ k I :=
  Hom.of (AlgHom.pullbackSnd (toResidue A).hom (squareZeroToResidue Λ k I).hom)
    (instIsLocalHom_squareZeroPullbackSnd A I) sorry

/-- The canonical section `A ⟶ A ×_k k[I]` of the first projection. -/
noncomputable def squareZeroPullbackSection : A ⟶ squareZeroPullback A I :=
  Hom.of (squareZeroPullbackSectionHom A I) (instIsLocalHom_squareZeroPullbackSectionHom A I)
    sorry

/-- The composite `A ×_k k[I] ⟶ B` of the first projection with a further map `A ⟶ B`. -/
noncomputable abbrev squareZeroPullbackToBase {B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    squareZeroPullback A I ⟶ B :=
  squareZeroPullbackFst A I ≫ f

/-- The composite `A ×_k k[I] ⟶ k` of the second projection with `k[I] ⟶ k`. -/
noncomputable abbrev squareZeroPullbackSndToResidue :
    squareZeroPullback A I ⟶ residue Λ k :=
  squareZeroPullbackSnd A I ≫ squareZeroToResidue Λ k I

/-- The underlying algebra map of `squareZeroPullbackFst` is the first algebra projection. -/
theorem squareZeroPullbackFst_hom :
    (squareZeroPullbackFst A I).hom =
      AlgHom.pullbackFst (toResidue A).hom (squareZeroToResidue Λ k I).hom := sorry

/-- The underlying algebra map of `squareZeroPullbackSnd` is the second algebra projection. -/
theorem squareZeroPullbackSnd_hom :
    (squareZeroPullbackSnd A I).hom =
      AlgHom.pullbackSnd (toResidue A).hom (squareZeroToResidue Λ k I).hom := sorry

/-- The canonical section is a section of the first projection. -/
theorem squareZeroPullbackSection_comp_fst :
    squareZeroPullbackSection A I ≫ squareZeroPullbackFst A I = 𝟙 A := sorry

/-- The square-zero cospan square is a pullback in `ArtinianLocalAlgCat`. -/
theorem isPullback_squareZeroPullback :
    IsPullback (squareZeroPullbackFst A I) (squareZeroPullbackSnd A I)
      (toResidue A) (squareZeroToResidue Λ k I) := sorry

/-- The two projections of `A ×_k k[I]` agree after composing to the residue field. -/
theorem squareZeroPullbackFst_comp_toResidue :
    squareZeroPullbackFst A I ≫ toResidue A =
      squareZeroPullbackSnd A I ≫ squareZeroToResidue Λ k I := sorry

end ArtinianLocalAlgCat
