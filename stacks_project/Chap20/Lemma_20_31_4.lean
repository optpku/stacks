module

public import stacks_project.Chap20.Lemma_20_25_1
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductNaive

/-! @stack 0FKV -/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {ι : Type u}

-- Local declaration justification (source-local notation): the coefficient category in 0FKV.
local notation "ΓModX" => ModuleCat (globalSectionsRing X)
-- Local declaration justification (source-local notation): the source complexes in 0FKV.
local notation "KplusMod" => CochainComplex.Plus (RingedSpace.Modules X)
-- Local declaration justification (source-local notation): the source derived category in 0FKV.
local notation "DplusModX" => DerivedCategory.Plus (RingedSpace.Modules X)
-- Local declaration justification (source-local notation): the target derived category in 0FKV.
local notation "DplusΓX" => DerivedCategory.Plus ΓModX

/- Domain-style sampling for Lemma 20.31.4:
- primary domain: the bounded-below Čech/global-sections tensor square on a ringed space;
- sampled owner declarations:
  `moduleCechDerivedFunctor`,
  `IsModuleCechToDerivedGlobalSectionsComparison`,
  `exists_moduleCechToDerivedGlobalSections`,
  `relativeDerivedCupProduct`,
  `DerivedPushforwardTensorNaiveCup.commSqOfMate`;
- source/core/bridge triage:
  `source-facing`: the bounded-below Čech/global-sections specialization for a comparison
    `τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus`;
  `core/canonical`: `DerivedPushforwardTensorNaiveCup` and its theorem `commSqOfMate`;
  `bridge/view`: the existence statement below for the Chapter 20 Čech/global-sections comparison
    of Lemma `20.25.1`.

Primitive data are the Čech comparison morphism `τ`, the bounded-below tensor representatives on
the Čech and source sides, and the pullback-side compatibility square. The commuting tensor square
itself is already owned by `ReasLib.CategoryTheory.Adjunction.RelativeCupProductNaive`, so this
file keeps only the source-facing corollary choosing `τ` from Lemma `20.25.1`. -/

variable (𝒰 : ι → Opens X.carrier)

-- Local declaration justification (source-local notation): the localization used in 0FKV.
-- Local declaration justification (source-local notation): the source realization in 0FKV.
local notation "KplusToDplusModX" =>
  (DerivedCategory.Plus.Q : KplusMod ⥤ DplusModX)
-- Local declaration justification (source-local notation): the target functor `RΓ` in 0FKV.
local notation "RΓplus" => Module.Derived.GlobalSections.Bounded.functor X
-- Local declaration justification (source-local notation): the total Čech functor in 0FKV.
local notation "CechF" => moduleCechDerivedFunctor X 𝒰

#check @CategoryTheory.DerivedPushforwardTensorNaiveCup.commSqOfMate

/-- Lemma 20.31.4 (0FKV): assuming the mate compatibility furnished by Lemma `20.31.3`, one
Čech/global-sections comparison supplied by Lemma `20.25.1` simultaneously makes the
tensor/naive-cup-product square commute for all bounded-below complexes. -/
@[stacks 0FKV]
theorem exists_moduleCechToDerivedGlobalSections_tensor_naiveCupProduct_commSq
    (h𝒰 : iSup 𝒰 = ⊤)
    (leftDerivedPullback : DplusΓX ⥤ DplusModX)
    (globalSectionsAdj : leftDerivedPullback ⊣ RΓplus)
    (derivedTensorX : DplusModX ⥤ DplusModX ⥤ DplusModX)
    (derivedTensorΓ : DplusΓX ⥤ DplusΓX ⥤ DplusΓX)
    (pullbackTensorIso :
      ∀ A B : DplusΓX,
        leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj
            (leftDerivedPullback.obj A)))
    (sourceTensorComplex : KplusMod → KplusMod → KplusMod)
    (cechTensorComplex : KplusMod → KplusMod → DplusΓX)
    (cechTensorCounit :
      ∀ K M : KplusMod,
        ((derivedTensorΓ.obj ((CechF).obj M)).obj
          ((CechF).obj K)) ⟶
          cechTensorComplex K M)
    (naiveCupProduct :
      ∀ K M : KplusMod,
        cechTensorComplex K M ⟶ (CechF).obj (sourceTensorComplex K M))
    (sourceTensorCounit :
      ∀ K M : KplusMod, ((derivedTensorX.obj ((KplusToDplusModX).obj M)).obj
          ((KplusToDplusModX).obj K)) ⟶
            (KplusToDplusModX).obj (sourceTensorComplex K M))
    (mateCompatibility :
      ∀ τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus,
        IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ →
        ∀ K M : KplusMod,
          CommSq
            (leftDerivedPullback.map
              (DerivedPushforwardTensorNaiveCup.top
                derivedTensorΓ (KplusToDplusModX).obj id (CechF).obj τ.app K M))
            (leftDerivedPullback.map
              (DerivedPushforwardTensorNaiveCup.left
                derivedTensorΓ id (CechF).obj sourceTensorComplex cechTensorComplex
                cechTensorCounit naiveCupProduct K M))
            (globalSectionsAdj.rightAdjointTensorMapAdjointOf
                derivedTensorΓ derivedTensorX
                (fun A B ↦ (pullbackTensorIso B A).hom)
                ((KplusToDplusModX).obj M)
                ((KplusToDplusModX).obj K) ≫
              sourceTensorCounit K M)
            ((globalSectionsAdj.homEquiv
                ((CechF).obj (sourceTensorComplex K M))
                ((KplusToDplusModX).obj (sourceTensorComplex K M))).symm
              (τ.app (sourceTensorComplex K M)))) :
    ∃ τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧
      ∀ K M : KplusMod,
        CommSq
          (DerivedPushforwardTensorNaiveCup.top
            derivedTensorΓ (KplusToDplusModX).obj id (CechF).obj τ.app K M)
          (DerivedPushforwardTensorNaiveCup.left
            derivedTensorΓ id (CechF).obj sourceTensorComplex cechTensorComplex
            cechTensorCounit naiveCupProduct K M)
          (DerivedPushforwardTensorNaiveCup.right
            globalSectionsAdj derivedTensorX derivedTensorΓ pullbackTensorIso
            (KplusToDplusModX).obj sourceTensorComplex sourceTensorCounit K M)
          (DerivedPushforwardTensorNaiveCup.bottom
            (KplusToDplusModX).obj id (CechF).obj sourceTensorComplex τ.app K M) := sorry

end

end AlgebraicGeometry.RingedSpace
