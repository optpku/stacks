module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic

/-!
# Base change of standard ph coverings

This module constructs the standard ph covering obtained by pulling a standard
ph covering back along a morphism of affine schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.StandardPhCovering

/-- The standard ph covering obtained by base-changing a standard ph covering along a
morphism of affine schemes. -/
noncomputable def pullback {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (Φ : StandardPhCovering T) (g : T' ⟶ T) : StandardPhCovering T' where
  m := Φ.m
  source := CategoryTheory.Limits.pullback Φ.toBase g
  toBase := pullback.snd Φ.toBase g
  isProper_toBase :=
    CategoryTheory.MorphismProperty.pullback_snd
      (P := @IsProper) Φ.toBase g Φ.isProper_toBase
  surjective_toBase :=
    CategoryTheory.MorphismProperty.pullback_snd
      (P := @Surjective) Φ.toBase g Φ.surjective_toBase
  cover := fun j ↦
    ⟨Scheme.baseChangeOpenFamily Φ.toBase g
        (fun i ↦ (Φ.cover i : Φ.source.Opens)) j,
      Scheme.isAffineOpen_baseChangeOpenFamily_of_isAffineHom Φ.toBase g
        (fun i ↦ (Φ.cover i : Φ.source.Opens)) (fun i ↦ (Φ.cover i).2) j⟩
  cover_eq_top :=
    Scheme.isOpenCover_baseChangeOpenFamily Φ.toBase g
      (fun i ↦ (Φ.cover i : Φ.source.Opens)) Φ.cover_eq_top

/-- The canonical isomorphism from a base-changed chart to the corresponding chart of the
base-changed standard ph covering. -/
noncomputable def pullbackObjIso {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (Φ : StandardPhCovering T) (g : T' ⟶ T) (j : Fin Φ.m) :
    CategoryTheory.Limits.pullback (Φ.map j) g ≅ (Φ.pullback g).obj j :=
  (pullbackRightPullbackFstIso Φ.toBase g
      ((Φ.cover j : Φ.source.Opens)).ι).symm ≪≫
    pullbackSymmetry ((Φ.cover j : Φ.source.Opens)).ι
      (pullback.fst Φ.toBase g) ≪≫
    pullbackRestrictIsoRestrict (pullback.fst Φ.toBase g)
      (Φ.cover j : Φ.source.Opens)

/-- Base change of every chart map in a standard ph covering agrees, through the canonical
chart isomorphism, with the corresponding map of the base-changed covering. -/
theorem pullbackFamily {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (Φ : StandardPhCovering T) (g : T' ⟶ T) (j : Fin Φ.m) :
    pullback.snd (Φ.map j) g =
      (Φ.pullbackObjIso g j).hom ≫ (Φ.pullback g).map j := sorry

end AlgebraicGeometry.StandardPhCovering
