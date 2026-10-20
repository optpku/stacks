/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImageStalk
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity
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

/-- The projection from the geometric fibre over `tbar` to the henselized fibre. -/
def cospecializationH :
    pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom ⟶
      henselizedFiber f sbar Rsh :=
  pullback.fst (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom

/-- The geometric-fibre projection is the first projection of the chosen pullback. -/
theorem cospecializationH_def :
    cospecializationH f sbar Rsh tbar =
      pullback.fst (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom :=
  rfl

-- Local declaration justification (metaprogramming implementation): The private specialization fixes the Grothendieck universe for exposed cochain-derived constructions.
set_option backward.privateInPublic true in
/-- Abelian étale direct image admits its cochain total right derived functor. -/
private instance (priority := 2000) directImageHasDerived {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (Cochain.toDerived (Etale.Abelian.directImage g)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ)) :=
  Cochain.hasDerived.{u + 1} (Etale.Abelian.directImage g)

-- Local declaration justification (metaprogramming implementation): The exposed functor uses the private universe-fixed derivability proof, without exposing an extra assumption.
set_option backward.privateInPublic true in
/-- The total right derived functor `Rh_*` of étale direct image. -/
abbrev derivedDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    Complexes Y ⥤ Complexes Z :=
  Cochain.functor (Etale.Abelian.directImage g)

-- Local declaration justification (metaprogramming implementation): The computation statement uses the same private universe-fixed derivability proof as the exposed functor.
set_option backward.privateInPublic true in
/-- Derived direct image is the cochain-level total right derived functor. -/
theorem derivedDirectImage_def {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    derivedDirectImage g = Cochain.functor (Etale.Abelian.directImage g) :=
  rfl

-- Local declaration justification (metaprogramming implementation): The private identity-derived witness must be available to the exposed derived-unit construction.
set_option backward.privateInPublic true in
/-- The identity of the derived category is the right derived functor of `Q`. -/
private instance isRightDerived_id_Q (Y : Scheme.{u}) :
    (𝟭 (Complexes Y)).IsRightDerivedFunctor
      (Functor.rightUnitor
        (DerivedCategory.Q : CochainComplex (Coefficients Y) ℤ ⥤ Complexes Y)).inv
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))
    (𝟭 (Complexes Y)) (Functor.rightUnitor DerivedCategory.Q)

-- Local declaration justification (metaprogramming implementation): The exposed cochain comparison uses the private universe-fixed derivability proof.
set_option backward.privateInPublic true in
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
        (Etale.Abelian.adjunction (cospecializationH f sbar Rsh tbar)).unit
        (ComplexShape.up ℤ))
      DerivedCategory.Q ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (inverseImage (cospecializationH f sbar Rsh tbar) ⋙
            Etale.Abelian.directImage (cospecializationH f sbar Rsh tbar)))
        (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((inverseImage (cospecializationH f sbar Rsh tbar)).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Cochain.unit (Etale.Abelian.directImage (cospecializationH f sbar Rsh tbar))) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (inverseImage (cospecializationH f sbar Rsh tbar)).mapDerivedCategoryFactors.inv
      (derivedDirectImage (cospecializationH f sbar Rsh tbar)) ≫
    (Functor.associator _ _ _).hom

-- Local declaration justification (metaprogramming implementation): The exposed descent uses the private proved identity-derived witness.
set_option backward.privateInPublic true in
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

/-- The comparison `β_{K,sbar,tbar} : K|_{Xsh} ⟶ Rh_*(K|_{X_tbar})`, using
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
        ((derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K) :=
  rfl

end AlgebraicGeometry.Scheme.EtaleVanishingCycles

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

variable {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))
variable (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
variable (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom)

/-- For bounded-below étale coefficients relative to which a morphism is locally acyclic,
the inverse image of the cospecialization comparison on the closed geometric fibre is invertible. -/
theorem isIso_inverseImage_etaleCohomologyBeta (K : Complexes X)
    (hK : t.plus K) [LocallyAcyclicRelative f K] :
    IsIso ((derivedInverseImage (geometricFiberToHenselized f sbar Rsh iS hiS)).map
      (etaleCohomologyBeta f sbar Rsh tbar K)) := sorry

end AlgebraicGeometry.Scheme
