module

public import stacks_project.Chap59.«59_93_0_1_Comparison»
public import stacks_project.Chap59.Theorem_59_53_1
public import stacks_project.Chap59.Remark_59_75_8_Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open DerivedCategory.TStructure

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleVanishingCycles

variable {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))

/-- The source map `h : X_tbar ⟶ Xsh` of the cospecialization setup, as the
chosen first projection of `X_tbar = Xsh ×_{Spec(O^sh)} Spec(κ(tbar))`. -/
def cospecializationH :
    pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom ⟶
      henselizedFiber f sbar Rsh :=
  pullback.fst (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom

/-- `h` is the first projection of the geometric fibre of `tbar` over `Xsh`. -/
theorem cospecializationH_def :
    cospecializationH f sbar Rsh tbar =
      pullback.fst (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom :=
  rfl

/-- The source map `i : X_sbar ⟶ Xsh` of the cospecialization setup. -/
abbrev cospecializationI
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
    (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom) :
    pullback f sbar.hom ⟶ henselizedFiber f sbar Rsh :=
  geometricFiberToHenselized f sbar Rsh iS hiS

/-- `i` is the existing geometric-fibre comparison into the henselized fibre. -/
theorem cospecializationI_def
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
    (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom) :
    cospecializationI f sbar Rsh iS hiS =
      geometricFiberToHenselized f sbar Rsh iS hiS :=
  rfl

/-- Étale direct image on abelian sheaves, right adjoint to inverse image. -/
abbrev directImage {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    Coefficients Y ⥤ Coefficients Z :=
  (smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    Z.smallEtaleTopology Y.smallEtaleTopology

/-- Direct image is the continuous sheaf pushforward of the small étale pullback functor. -/
theorem directImage_def {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    directImage g =
      (smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        Z.smallEtaleTopology Y.smallEtaleTopology :=
  rfl

/-- Direct image of abelian étale sheaves is additive. -/
instance directImage_additive {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (directImage g).Additive := sorry

/-- The total right derived functor `Rh_*` of étale direct image. -/
abbrev derivedDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [HasRightDerivedFunctor (Cochain.toDerived (directImage g))
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))] :
    Complexes Y ⥤ Complexes Z :=
  Cochain.functor (directImage g)

/-- Derived direct image is the cochain-level total right derived functor. -/
theorem derivedDirectImage_def {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [HasRightDerivedFunctor (Cochain.toDerived (directImage g))
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))] :
    derivedDirectImage g = Cochain.functor (directImage g) :=
  rfl

variable
    [((smallEtalePullback (cospecializationH f sbar Rsh tbar)).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (henselizedFiber f sbar Rsh).smallEtaleTopology
        (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh))
          tbar.hom).smallEtaleTopology).IsRightAdjoint]
    [HasRightDerivedFunctor
      (Cochain.toDerived (directImage (cospecializationH f sbar Rsh tbar)))
      (HomologicalComplex.quasiIso
        (Coefficients
          (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom))
        (ComplexShape.up ℤ))]

/-- The identity of the derived category is the right derived functor of `Q`. -/
instance isRightDerived_id_Q (Y : Scheme.{u}) :
    (𝟭 (Complexes Y)).IsRightDerivedFunctor
      (Functor.rightUnitor
        (DerivedCategory.Q : CochainComplex (Coefficients Y) ℤ ⥤ Complexes Y)).inv
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ)) := sorry

/-- The cochain-level comparison presenting the derived adjunction unit of
`h^{-1} ⊣ Rh_*`. -/
def derivedAdjunctionUnitCochain :
    (DerivedCategory.Q :
        CochainComplex (Coefficients (henselizedFiber f sbar Rsh)) ℤ ⥤
          Complexes (henselizedFiber f sbar Rsh)) ⟶
      DerivedCategory.Q ⋙
        derivedInverseImage (cospecializationH f sbar Rsh tbar) ⋙
          derivedDirectImage (cospecializationH f sbar Rsh tbar) :=
  Functor.whiskerRight
      (Functor.mapHomologicalComplexIdIso (Coefficients (henselizedFiber f sbar Rsh))
          (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        (((smallEtalePullback (cospecializationH f sbar Rsh tbar)).sheafAdjunctionContinuous
            AddCommGrpCat.{u + 1} (henselizedFiber f sbar Rsh).smallEtaleTopology
            (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh))
              tbar.hom).smallEtaleTopology).unit)
        (ComplexShape.up ℤ))
      DerivedCategory.Q ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (inverseImage (cospecializationH f sbar Rsh tbar) ⋙
            directImage (cospecializationH f sbar Rsh tbar)))
        (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((inverseImage (cospecializationH f sbar Rsh tbar)).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Cochain.unit (directImage (cospecializationH f sbar Rsh tbar))) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (inverseImage (cospecializationH f sbar Rsh tbar)).mapDerivedCategoryFactors.inv
      (derivedDirectImage (cospecializationH f sbar Rsh tbar)) ≫
    (Functor.associator _ _ _).hom

/-- The derived adjunction unit `K|_{Xsh} ⟶ Rh_*(h^{-1}(K|_{Xsh}))`. -/
def derivedAdjunctionUnit :
    𝟭 (Complexes (henselizedFiber f sbar Rsh)) ⟶
      derivedInverseImage (cospecializationH f sbar Rsh tbar) ⋙
        derivedDirectImage (cospecializationH f sbar Rsh tbar) :=
  (𝟭 (Complexes (henselizedFiber f sbar Rsh))).rightDerivedDesc
    (Functor.rightUnitor
      (DerivedCategory.Q :
        CochainComplex (Coefficients (henselizedFiber f sbar Rsh)) ℤ ⥤
          Complexes (henselizedFiber f sbar Rsh))).inv
    (HomologicalComplex.quasiIso (Coefficients (henselizedFiber f sbar Rsh))
      (ComplexShape.up ℤ))
    (derivedInverseImage (cospecializationH f sbar Rsh tbar) ⋙
      derivedDirectImage (cospecializationH f sbar Rsh tbar))
    (derivedAdjunctionUnitCochain f sbar Rsh tbar)

/-- 59.94: the comparison `β_{K,sbar,tbar} : K|_{Xsh} ⟶ Rh_*(K|_{X_tbar})`, using
`K|_{X_tbar} = h^{-1}(K|_{Xsh})`. -/
def etaleCohomologyBeta (K : Complexes X) :
    (derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K ⟶
      (derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
        ((derivedInverseImage (cospecializationH f sbar Rsh tbar)).obj
          ((derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K)) :=
  (derivedAdjunctionUnit f sbar Rsh tbar).app
    ((derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K)

/-- The derived adjunction unit is induced from the cochain-level comparison. -/
theorem derivedAdjunctionUnitCochain_comp_Q :
    Functor.whiskerLeft DerivedCategory.Q (derivedAdjunctionUnit f sbar Rsh tbar) =
      derivedAdjunctionUnitCochain f sbar Rsh tbar := sorry

/-- `β` is the derived adjunction unit of `h^{-1} ⊣ Rh_*` on `K|_{Xsh}`. -/
theorem etaleCohomologyBeta_app (K : Complexes X) :
    etaleCohomologyBeta f sbar Rsh tbar K =
      (derivedAdjunctionUnit f sbar Rsh tbar).app
        ((derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K) := sorry

end AlgebraicGeometry.Scheme.EtaleVanishingCycles
