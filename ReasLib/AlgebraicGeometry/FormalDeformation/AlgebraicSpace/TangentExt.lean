/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.DualNumber.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.IsoClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.Automorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.ExtZero

/-! # Infinitesimal automorphisms and tangent classes of algebraic spaces via cotangent extensions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor Limits
open Functor.Fiber
open ArtinianLocalAlgCat
open AlgebraicGeometry.AlgebraicSpace.Thickening
open AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
open TrivSqZeroExt
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraicSpaceCat

variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))


/-- The trivial dual-number lift of the structure morphism as a flat first-order thickening lift. -/
def trivialFlatLift :
    FlatLift (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom :=
  FlatLift.of (trivialSpaceOver Λ k X) (trivialSpaceImmersion Λ k X) sorry

/-- Identification `f^* 𝒞_{Spec k / Spec k[ε]} ≅ 𝒪_X` for the trivial dual-number
thickening, via the ε-coefficient isomorphism `ker(k[ε] → k) ≅ k`. -/
def pulledConormalUnitIso :
    pulledConormal (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom ≅
      SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space) :=
  (Modules.pullback ((ofResidue Λ k X).structureHom ≫ specMap (dualNumberToResidue Λ k))).mapIso
      (conormalToIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
    (Modules.pullbackCompIso (ofResidue Λ k X).structureHom
        (specMap (dualNumberToResidue Λ k))).symm.app
      (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ≪≫
    (Modules.pullback (ofResidue Λ k X).structureHom).mapIso (residueKernelIsoUnit Λ k) ≪≫
    (Modules.structureModulePullbackIso (ofResidue Λ k X).structureHom).symm

/-- Ext⁰ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extZero :=
  Ext⁽(0 : ℤ)⁾((DerivedCategory.Q).obj NL[(ofResidue Λ k X).structureHom],
    (DerivedCategory.Q).obj
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).obj
        (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))))

/-- Ext¹ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extOne :=
  Ext⁽(1 : ℤ)⁾((DerivedCategory.Q).obj NL[(ofResidue Λ k X).structureHom],
    (DerivedCategory.Q).obj
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).obj
        (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))))

/-- Transport Ext⁰ of `f^* 𝒞` to Ext⁰ of `𝒪_X`. -/
def extZeroOfNL
    (ξ : extZeroNL (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom) :
    extZero Λ k X :=
  ξ ≫ (shiftFunctor (DerivedCategory (Modules (ofResidue Λ k X).space)) (0 : ℤ)).map
    (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).map
        (pulledConormalUnitIso Λ k X).hom))

/-- Transport Ext¹ of `𝒪_X` to Ext¹ of `f^* 𝒞`. -/
def extOneNLOf (ξ : extOne Λ k X) :
    extOneNL (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom :=
  ξ ≫ (shiftFunctor (DerivedCategory (Modules (ofResidue Λ k X).space)) (1 : ℤ)).map
    (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).map
        (pulledConormalUnitIso Λ k X).inv))

/-- Automorphisms of the trivial lift reducing to the identity on `X`, from `Inf(Def_X)`. -/
def infToReduceIdAuto (α : inf Λ k X) : ReduceIdAuto (trivialFlatLift Λ k X) :=
  let hom : (trivialFlatLift Λ k X).space ⟶ (trivialFlatLift Λ k X).space :=
    (fiberInclusion.map α.val.hom).spaceHom
  let laws :
      (hom ≫ (trivialFlatLift Λ k X).f' = (trivialFlatLift Λ k X).f') ∧
      ((trivialFlatLift Λ k X).i ≫ hom = (trivialFlatLift Λ k X).i) ∧ IsIso hom := sorry
  { hom := hom
    over := laws.1
    restrict := laws.2.1
    isIso := laws.2.2 }

/-- The comparison `Inf(Def_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`. -/
def infToExtZero : inf Λ k X → extZero Λ k X :=
  fun α ↦ extZeroOfNL Λ k X
    (reduceIdAutoEquiv (trivialFlatLift Λ k X) (infToReduceIdAuto Λ k X α))

/-- The dual-number fibre object of `Def_X` associated to a flat first-order lift. -/
def ofFlatLift
    (L : FlatLift (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom) :
    (deformationForget Λ k X).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X).obj
        (Over.mk
          (FlatAlgebraicSpaceCat.Hom.of (dualNumberToResidue Λ k) L.i L.isPullback.flip :
            FlatAlgebraicSpaceCat.of (dualNumber Λ k) L.space L.f' L.flat ⟶
              fiberInclusion.obj (residueObj Λ k X))) =
      dualNumber Λ k)

/-- Isomorphism classes of flat lifts map to tangent vectors of `Def_X`. -/
def ofIsoClass :
    IsoClass (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom →
      tangentSpace Λ k X :=
  Quotient.lift (fun L ↦ tangentSpaceMk Λ k X (ofFlatLift Λ k X L)) sorry

/-- The class of a lift is sent to the class of `ofFlatLift`. -/
theorem ofIsoClass_mk
    (L : FlatLift (specMap (dualNumberToResidue Λ k)) (ofResidue Λ k X).structureHom) :
    ofIsoClass Λ k X (isoClassMk L) =
      tangentSpaceMk Λ k X (ofFlatLift Λ k X L) :=
  sorry

/-- The comparison `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ T Def_X`. -/
def ofExtOne : extOne Λ k X → tangentSpace Λ k X :=
  fun ξ ↦ ofIsoClass Λ k X
    (isoClassEquiv (trivialFlatLift Λ k X) (extOneNLOf Λ k X ξ))

/-- The zero Ext¹ class is sent to the trivial tangent vector. -/
theorem ofExtOne_zero : ofExtOne Λ k X 0 = trivialTangent Λ k X :=
  sorry

/-- Infinitesimal automorphisms of an algebraic space correspond bijectively to Ext⁰ of its naive cotangent complex with structure-module coefficients. -/
theorem infToExtZero_bijective :
    Function.Bijective (infToExtZero Λ k X) := sorry

/-- Ext¹ of the naive cotangent complex with structure-module coefficients parametrizes tangent classes of algebraic-space deformations. -/
theorem ofExtOne_bijective :
    Function.Bijective (ofExtOne Λ k X) := sorry

end FlatAlgebraicSpaceCat
