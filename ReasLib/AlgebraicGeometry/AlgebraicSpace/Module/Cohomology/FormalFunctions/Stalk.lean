/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.GlobalSections
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.FlatBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-!
# Completed geometric-stalk comparison for formal functions

The maps from the geometric stalk of `R^p f_* F` to the infinitesimal neighbourhood
cohomology groups `H^p(X_n, F_n)` assemble to a morphism from the `m_ȳ`-adic
completion to the inverse limit, as modules over `O_{Y,ȳ}^∧`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ModuleSpecΓ
open TopologicalSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace
namespace FormalFunctions

variable (f : X ⟶ Y) (F : X.Modules) (ybar : GeometricPoint Y)

/-- Affine-base cohomology `H^p(X_n, F_n)` as a module over `O_{Y,ȳ}/m^n`. -/
def cohomology [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (thickening ybar n).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules] :
    ModuleCat
      (etaleLocalRing Y ybar ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n) :=
  Modules.cohomologyOver (quotientToSpec ybar n ≫ specHom ybar)
    (toSpec f ybar n) (sheaf f F ybar n) p

/-- `cohomology f F ybar p n` is affine-base cohomology of `F_n` on `X_n`. -/
theorem cohomology_eq [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (thickening ybar n).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules] :
    cohomology f F ybar p n =
      Modules.cohomologyOver (quotientToSpec ybar n ≫ specHom ybar)
        (toSpec f ybar n) (sheaf f F ybar n) p :=
  rfl

/-- Pullback of `F` along `spaceStep ≫ i_{n+1}` recovers `F_n`. -/
theorem sheaf_spaceStep_comp [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (spaceStep f ybar n ≫ toX f ybar (n + 1))).obj F =
      sheaf f F ybar n :=
  sorry

/-- Identification `F_n ≅ spaceStep^* F_{n+1}` from `i_n = spaceStep ≫ i_{n+1}`. -/
private def sheafStepPullback [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (spaceStep f ybar n)).obj (sheaf f F ybar (n + 1)) ⟶
      sheaf f F ybar n :=
  (pullbackCompIso (spaceStep f ybar n) (toX f ybar (n + 1))).hom.app F ≫
    eqToHom
      (congrArg (fun i ↦ (Modules.pullback i).obj F)
        (by exact pullback.lift_fst _ _ _))

/-- Adjunction unit `F_{n+1} ⟶ spaceStep_* F_n`. -/
private def sheafUnit [IsLocallyNoetherian Y] (n : ℕ) :
    sheaf f F ybar (n + 1) ⟶
      (pushforward (spaceStep f ybar n)).obj (sheaf f F ybar n) :=
  (pullbackPushforwardAdjunction (spaceStep f ybar n)).unit.app (sheaf f F ybar (n + 1)) ≫
    (pushforward (spaceStep f ybar n)).map (sheafStepPullback f F ybar n)

/-- Pushforward along an infinitesimal neighbourhood transition preserves homology. -/
instance instPreservesHomology_pushforward_spaceStep [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules] :
    (pushforward (spaceStep f ybar n)).PreservesHomology :=
  sorry

/-- Pushforward along a thickening transition preserves homology. -/
instance instPreservesHomology_pushforward_thickeningStep [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules] :
    (pushforward (thickeningStep ybar n)).PreservesHomology :=
  sorry

/-- Leray comparison of higher direct images along `spaceStep` and `thickeningStep`. -/
private def higherDirectImagePushforward [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (space f ybar (n + 1)).Modules] :
    Modules.higherDirectImage (toSpec f ybar (n + 1))
        ((pushforward (spaceStep f ybar n)).obj (sheaf f F ybar n)) p ⟶
      (pushforward (thickeningStep ybar n)).obj
        (Modules.higherDirectImage (toSpec f ybar n) (sheaf f F ybar n) p) :=
  (Modules.closedImmersionLerayIso (spaceStep f ybar n) (toSpec f ybar (n + 1))
      (sheaf f F ybar n) p).inv ≫
    (NatIso.rightDerived
        (eqToIso (congrArg pushforward
          (by exact pullback.lift_snd _ _ _))) p).hom.app
      (sheaf f F ybar n) ≫
    (NatIso.rightDerived
        (pushforwardComp (toSpec f ybar n) (thickeningStep ybar n)).symm p).hom.app
      (sheaf f F ybar n) ≫
    (Functor.RightDerived.postcompObjIso (pushforward (toSpec f ybar n))
        (pushforward (thickeningStep ybar n)) p (sheaf f F ybar n)).hom

/-- After pushing `F_n` forward along `spaceStep`, affine-base cohomology maps to
restriction of scalars of `H^p(X_n, F_n)`. -/
private def cohomologyOverPushforward [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (space f ybar (n + 1)).Modules] :
    Modules.cohomologyOver (quotientToSpec ybar (n + 1) ≫ specHom ybar)
        (toSpec f ybar (n + 1))
        ((pushforward (spaceStep f ybar n)).obj (sheaf f F ybar n)) p ⟶
      (ModuleCat.restrictScalars (quotientFactor ybar n)).obj
        (cohomology f F ybar p n) :=
  (moduleSpecΓFunctor
      (R := CommRingCat.of
        (etaleLocalRing Y ybar ⧸
          IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ (n + 1)))).map
    ((toScheme (Over.mk (quotientToSpec ybar (n + 1) ≫ specHom ybar))).map
        (higherDirectImagePushforward f F ybar p n) ≫
      toScheme_pushforwardHom
        (quotientToSpec ybar (n + 1) ≫ specHom ybar)
        (quotientToSpec ybar n ≫ specHom ybar)
        (quotientFactor_specHom ybar n)
        (Modules.higherDirectImage (toSpec f ybar n) (sheaf f F ybar n) p)) ≫
    (ModuleSpecΓ.pushforwardIso
        (CommRingCat.ofHom (quotientFactor ybar n))).hom.app
      ((toScheme (Over.mk (quotientToSpec ybar n ≫ specHom ybar))).obj
        (Modules.higherDirectImage (toSpec f ybar n) (sheaf f F ybar n) p))

/-- The `O_{Y,ȳ}/m^{n+1}`-linear restriction
`H^p(X_{n+1}, F_{n+1}) ⟶ restrictScalars (H^p(X_n, F_n))`. -/
@[no_expose]
def cohomologyStepOver [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (space f ybar (n + 1)).Modules] :
    cohomology f F ybar p (n + 1) ⟶
      (ModuleCat.restrictScalars (quotientFactor ybar n)).obj
        (cohomology f F ybar p n) :=
  (moduleSpecΓFunctor
      (R := CommRingCat.of (etaleLocalRing Y ybar ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ (n + 1)))).map
    ((toScheme (Over.mk (quotientToSpec ybar (n + 1) ≫ specHom ybar))).map
      (higherDirectImageMap (toSpec f ybar (n + 1)) (sheafUnit f F ybar n) p)) ≫
    cohomologyOverPushforward f F ybar p n

/-- Neighbourhood cohomology as an `O_{Y,ȳ}^∧`-module by restriction of scalars. -/
def completedCohomology [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (thickening ybar n).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules] :
    ModuleCat
      (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
        (etaleLocalRing Y ybar)) :=
  (ModuleCat.restrictScalars
      (AdicCompletion.evalₐ
        (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar)) n).toRingHom).obj
    (cohomology f F ybar p n)

/-- Evaluation `O_{Y,ȳ}^∧ ⟶ O_{Y,ȳ}/m^n` factors through the successor quotient. -/
theorem evalₐ_comp_quotientFactor [IsLocallyNoetherian Y] (n : ℕ) :
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar)) n).toRingHom =
      (quotientFactor ybar n).comp
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (n + 1)).toRingHom :=
  sorry

/-- The successor restriction `H^p(X_{n+1}, F_{n+1}) ⟶ H^p(X_n, F_n)` of
`O_{Y,ȳ}^∧`-modules. -/
def cohomologyStep [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (space f ybar (n + 1)).Modules] :
    completedCohomology f F ybar p (n + 1) ⟶ completedCohomology f F ybar p n :=
  (ModuleCat.restrictScalars
      (AdicCompletion.evalₐ
        (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar)) (n + 1)).toRingHom).map
    (cohomologyStepOver f F ybar p n) ≫
  (ModuleCat.restrictScalarsComp'
      (AdicCompletion.evalₐ
        (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar)) (n + 1)).toRingHom
      (quotientFactor ybar n)
      (AdicCompletion.evalₐ
        (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar)) n).toRingHom
      (evalₐ_comp_quotientFactor ybar n)).inv.app
    (cohomology f F ybar p n)

/-- Neighbourhood cohomology as a uniformly `ℕ`-indexed family of `O_{Y,ȳ}^∧`-modules. -/
private def completedCohomologySeq [IsLocallyNoetherian Y]
    [Abelian X.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules] (p : ℕ) :
    ℕ →
      ModuleCat
        (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (etaleLocalRing Y ybar)) :=
  fun n ↦ completedCohomology f F ybar p n

/-- Successor maps of neighbourhood cohomology as a uniformly indexed family. -/
private def cohomologyStepSeq [IsLocallyNoetherian Y]
    [Abelian X.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules] (p n : ℕ) :
    completedCohomologySeq f F ybar p (n + 1) ⟶ completedCohomologySeq f F ybar p n :=
  cohomologyStep f F ybar p n

/-- The inverse system `n ↦ H^p(X_n, F_n)` in `ModuleCat O_{Y,ȳ}^∧`. -/
def system [IsLocallyNoetherian Y]
    [Abelian X.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules] (p : ℕ) :
    SequentialInverseSystem
      (ModuleCat
        (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (etaleLocalRing Y ybar))) :=
  Functor.ofOpSequence (X := fun n ↦ completedCohomology f F ybar p n)
    (fun n ↦ cohomologyStep f F ybar p n)

/-- Stage `n` of `system` is neighbourhood cohomology of `F_n`. -/
theorem system_obj [IsLocallyNoetherian Y]
    [Abelian X.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules] (p n : ℕ) :
    (system f F ybar p).obj (op n) = completedCohomology f F ybar p n :=
  sorry

/-- The successor map of `system` is `cohomologyStep`. -/
theorem system_stepMap [IsLocallyNoetherian Y]
    [Abelian X.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules] (p n : ℕ) :
    (system f F ybar p).stepMap n = cohomologyStep f F ybar p n :=
  sorry

/-- Affine-base cohomology `H^p(X_∞, F_∞)` as an `O_{Y,ȳ}`-module. -/
def infCohomology [IsLocallyNoetherian Y] (p : ℕ)
    [Abelian X.Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    ModuleCat (etaleLocalRing Y ybar) :=
  Modules.cohomologyOver (specHom ybar) (toSpecInf f ybar)
    (sheafInf f F ybar) p

/-- Pullback of `F` along `toInf ≫ i_∞` recovers `F_n`. -/
theorem sheaf_toInf_comp [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (toInf f ybar n ≫ toXInf f ybar)).obj F =
      sheaf f F ybar n :=
  sorry

/-- Identification `F_n ≅ toInf^* F_∞` from `i_n = toInf ≫ i_∞`. -/
private def sheafInfPullback [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (toInf f ybar n)).obj (sheafInf f F ybar) ⟶
      sheaf f F ybar n :=
  (pullbackCompIso (toInf f ybar n) (toXInf f ybar)).hom.app F ≫
    eqToHom
      (congrArg (fun i ↦ (Modules.pullback i).obj F)
        (by exact pullback.lift_fst _ _ _))

/-- Adjunction unit `F_∞ ⟶ toInf_* F_n`. -/
private def sheafInfUnit [IsLocallyNoetherian Y] (n : ℕ) :
    sheafInf f F ybar ⟶ (pushforward (toInf f ybar n)).obj (sheaf f F ybar n) :=
  (pullbackPushforwardAdjunction (toInf f ybar n)).unit.app (sheafInf f F ybar) ≫
    (pushforward (toInf f ybar n)).map (sheafInfPullback f F ybar n)

/-- Pushforward along `X_n ⟶ X_∞` preserves homology. -/
instance instPreservesHomology_pushforward_toInf [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules] :
    (pushforward (toInf f ybar n)).PreservesHomology :=
  sorry

/-- Pushforward along `Spec(O/m^n) ⟶ Spec(O)` preserves homology. -/
instance instPreservesHomology_pushforward_toSpecSpace [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules] :
    (pushforward (toSpecSpace ybar n)).PreservesHomology :=
  sorry

/-- Leray comparison of higher direct images along `toInf` and `toSpecSpace`. -/
private def higherDirectImageInfPushforward [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    Modules.higherDirectImage (toSpecInf f ybar)
        ((pushforward (toInf f ybar n)).obj (sheaf f F ybar n)) p ⟶
      (pushforward (toSpecSpace ybar n)).obj
        (Modules.higherDirectImage (toSpec f ybar n) (sheaf f F ybar n) p) :=
  (Modules.closedImmersionLerayIso (toInf f ybar n) (toSpecInf f ybar)
      (sheaf f F ybar n) p).inv ≫
    (NatIso.rightDerived
        (eqToIso (congrArg pushforward
          (by exact pullback.lift_snd _ _ _))) p).hom.app
      (sheaf f F ybar n) ≫
    (NatIso.rightDerived
        (pushforwardComp (toSpec f ybar n) (toSpecSpace ybar n)).symm p).hom.app
      (sheaf f F ybar n) ≫
    (Functor.RightDerived.postcompObjIso (pushforward (toSpec f ybar n))
        (pushforward (toSpecSpace ybar n)) p (sheaf f F ybar n)).hom

/-- After pushing `F_n` forward along `toInf`, affine-base cohomology maps to
restriction of scalars of `H^p(X_n, F_n)`. -/
private def cohomologyOverInfPushforward [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    Modules.cohomologyOver (specHom ybar) (toSpecInf f ybar)
        ((pushforward (toInf f ybar n)).obj (sheaf f F ybar n)) p ⟶
      (ModuleCat.restrictScalars
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n))).obj
        (cohomology f F ybar p n) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).map
    ((toScheme (Over.mk (specHom ybar))).map
        (higherDirectImageInfPushforward f F ybar p n) ≫
      toScheme_pushforwardHom (specHom ybar)
        (quotientToSpec ybar n ≫ specHom ybar) rfl
        (Modules.higherDirectImage (toSpec f ybar n) (sheaf f F ybar n) p)) ≫
    (ModuleSpecΓ.pushforwardIso
        (CommRingCat.ofHom
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n)))).hom.app
      ((toScheme (Over.mk (quotientToSpec ybar n ≫ specHom ybar))).obj
        (Modules.higherDirectImage (toSpec f ybar n) (sheaf f F ybar n) p))

/-- The `O_{Y,ȳ}`-linear restriction `H^p(X_∞, F_∞) ⟶ restrictScalars (H^p(X_n, F_n))`. -/
@[no_expose]
def infToCohomology [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    infCohomology f F ybar p ⟶
      (ModuleCat.restrictScalars
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n))).obj
        (cohomology f F ybar p n) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).map
    ((toScheme (Over.mk (specHom ybar))).map
      (higherDirectImageMap (toSpecInf f ybar) (sheafInfUnit f F ybar n) p)) ≫
    cohomologyOverInfPushforward f F ybar p n

/-- Global sections of `c^* G` on `Spec(O_{Y,ȳ})`. -/
def pullbackGamma (ybar : GeometricPoint Y) (G : Y.Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    ModuleCat (etaleLocalRing Y ybar) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).obj
    ((toScheme (Over.mk (specHom ybar))).obj
      ((Modules.pullback (fromSpecEtaleLocalRing ybar)).obj G))

/-- The scheme morphism `Spec(O_{Y,ȳ}) ⟶ N` through the Zariski stalk of an étale
neighbourhood of `ȳ`. -/
private def neighborhoodFromSpec (ybar : GeometricPoint Y) (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (etaleLocalRing Y ybar)) ⟶ N.scheme :=
  Spec.map (CommRingCat.ofHom (etaleLocalRing_etaleNeighborhood.fromZariskiStalk N)) ≫
    N.scheme.fromSpecStalk N.center

/-- The scheme module on an étale neighbourhood of `Y` obtained by restricting `G`. -/
private def neighborhoodSchemeModule {Y : AlgebraicSpace S} (G : Y.Modules)
    (U : smallEtaleSite Y) : U.left.left.Modules :=
  (restrictToScheme U.left).obj ((Modules.pullback U.hom).obj G)

set_option maxHeartbeats 800000 in
/-- Restriction to the top open of a neighbourhood gives a map on sections. -/
private def presheafObjToNeighborhoodGamma {Y : AlgebraicSpace S} (G : Y.Modules)
    (U : smallEtaleSite Y) :
    G.val.presheaf.obj (op U) ⟶
      (Scheme.Modules.presheaf (neighborhoodSchemeModule G U)).obj
        (op (⊤ : U.left.left.Opens)) := by
  let V := RestrictToScheme.siteObject U.left (⊤ : U.left.left.Opens)
  let g : (restrictPostcompose U.hom).obj V ⟶ U :=
    MorphismProperty.CostructuredArrow.homMk
      (Yoneda.fullyFaithful.preimage V.hom) trivial (by
        change yoneda.map (Yoneda.fullyFaithful.preimage V.hom) ≫ U.hom = V.hom ≫ U.hom
        rw [Yoneda.fullyFaithful.map_preimage]
        rfl)
  let R := (restrictFunctor U.hom).obj G
  let e : (((restrictToScheme U.left).obj R).val.obj (op (⊤ : U.left.left.Opens))) ≃+
      R.val.obj (op V) :=
    { toEquiv := RestrictToScheme.sectionEquiv U.left R ⊤
      map_add' := by intros; rfl }
  let h : G.val.presheaf.obj (op U) ⟶
      (Scheme.Modules.presheaf ((restrictToScheme U.left).obj R)).obj
        (op (⊤ : U.left.left.Opens)) :=
    G.val.presheaf.map g.op ≫ AddCommGrpCat.ofHom e.symm.toAddMonoidHom
  exact h ≫
    Scheme.Modules.Hom.app
      ((restrictToScheme U.left).map
        ((restrictFunctorIsoPullback U.hom).hom.app G)) ⊤

/-- Scheme pullback sections map to sections on the strict-local spectrum
through the canonical restriction and composite-pullback comparisons. -/
private def neighborhoodPushforwardGammaHom (ybar : GeometricPoint Y) (G : Y.Modules)
    [hG : G.IsQuasicoherent] (U : smallEtaleSite Y) (l : OverLift ybar U)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    (Scheme.Modules.presheaf
        ((Scheme.Modules.pushforward
            (neighborhoodFromSpec ybar (SmallEtaleNeighborhood.of U l.hom l.fac))).obj
          ((Scheme.Modules.pullback
              (neighborhoodFromSpec ybar (SmallEtaleNeighborhood.of U l.hom l.fac))).obj
            (neighborhoodSchemeModule G U)))).obj
      (op (⊤ : U.left.left.Opens)) ⟶
      (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (pullbackGamma ybar G) := by
  let N := SmallEtaleNeighborhood.of U l.hom l.fac
  let a := neighborhoodFromSpec ybar N
  let t : Over.mk (specHom ybar) ⟶ U.left :=
    Over.homMk a (fromSpecToNeighborhood_w ybar N)
  let P := (Scheme.Modules.pullback a).obj (neighborhoodSchemeModule G U)
  let h : (⊤ : (Spec (CommRingCat.of (etaleLocalRing Y ybar))).Opens) ≤ a ⁻¹ᵁ ⊤ := by simp
  exact (Scheme.Modules.presheaf P).map (homOfLE h).op ≫
    Scheme.Modules.Hom.app
      (@RestrictToScheme.compositePullbackHom S Y (Over.mk (specHom ybar)) U.left
          U.hom t G hG ≫
        (restrictToScheme (Over.mk (specHom ybar))).map
          (eqToHom (congrArg (fun k ↦ (Modules.pullback k).obj G)
            (fromSpecEtaleLocalRing_spec ybar N).symm)) ≫
        (RestrictToScheme.restrictionIsoBare (Over.mk (specHom ybar))).hom.app
          ((Modules.pullback (fromSpecEtaleLocalRing ybar)).obj G)) ⊤

/-- The additive comparison from sections of `G` on an étale neighbourhood of `ȳ` to
`Γ(c^* G)`. -/
private def stalkToPullbackGammaComponent (ybar : GeometricPoint Y) (G : Y.Modules) [G.IsQuasicoherent]
    (U : smallEtaleSite Y) (l : OverLift ybar U)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    G.val.presheaf.obj (op U) ⟶
      (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (pullbackGamma ybar G) :=
  presheafObjToNeighborhoodGamma G U ≫
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction
          (neighborhoodFromSpec ybar (SmallEtaleNeighborhood.of U l.hom l.fac))).unit.app
        (neighborhoodSchemeModule G U))
      (⊤ : U.left.left.Opens) ≫
    neighborhoodPushforwardGammaHom ybar G U l

/-- Neighbourhood-section comparisons are natural in morphisms of the small étale site. -/
private theorem stalkToPullbackGammaComponent_w (ybar : GeometricPoint Y) (G : Y.Modules) [G.IsQuasicoherent]
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules]
    {U V : smallEtaleSite Y} (g : U ⟶ V) (l : OverLift ybar U) :
    G.val.presheaf.map g.op ≫ stalkToPullbackGammaComponent ybar G U l =
      stalkToPullbackGammaComponent ybar G V (OverLift.map g l) :=
  sorry

/-- Additive comparison from the étale stalk of `G` to global sections of `c^* G`. -/
private def stalkToPullbackGammaAdd (ybar : GeometricPoint Y) (G : Y.Modules) [G.IsQuasicoherent]
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    (toSmallEtalePoint ybar).presheafFiber.obj G.val.presheaf ⟶
      (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (pullbackGamma ybar G) :=
  (toSmallEtalePoint ybar).presheafFiberDesc
    (fun U l ↦ stalkToPullbackGammaComponent ybar G U l)
    (fun {U V} g l ↦ stalkToPullbackGammaComponent_w (U := U) (V := V) ybar G g l)

/-- The underlying function of the comparison `(R-module stalk) ⟶ Γ(c^* G)`. -/
private def stalkToPullbackGammaFun (ybar : GeometricPoint Y) (G : Y.Modules) [G.IsQuasicoherent]
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    stalkModuleCat ybar G → pullbackGamma ybar G :=
  fun x ↦
    ((Modules.stalkModuleCat_addIso ybar G).hom ≫
      stalkToPullbackGammaAdd ybar G).hom x

/-- The underlying function of `stalkToPullbackGamma` is linear over `O_{Y,ȳ}`. -/
private theorem isLinearMap_stalkToPullbackGammaFun (ybar : GeometricPoint Y) (G : Y.Modules) [G.IsQuasicoherent]
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    IsLinearMap (etaleLocalRing Y ybar) (stalkToPullbackGammaFun ybar G) :=
  sorry

/-- Comparison from the étale stalk of `G` to global sections of `c^* G`. -/
@[no_expose]
def stalkToPullbackGamma (ybar : GeometricPoint Y) (G : Y.Modules) [G.IsQuasicoherent]
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    stalkModuleCat ybar G ⟶ pullbackGamma ybar G :=
  ConcreteCategory.ofHom
    (IsLinearMap.mk' (stalkToPullbackGammaFun ybar G)
      (isLinearMap_stalkToPullbackGammaFun ybar G))

/-- Flat base change `c^* R^p f_* F ⟶ R^p f_∞_* F_∞` on global sections. -/
def pullbackGammaToInf [IsLocallyNoetherian Y] (p : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    pullbackGamma ybar (Modules.higherDirectImage f F p) ⟶ infCohomology f F ybar p :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).map
    ((toScheme (Over.mk (specHom ybar))).map
      (higherDirectImageBaseChangeHom (isPullbackInf f ybar) F p))

/-- Comparison `(R^p f_* F)_ȳ ⟶ H^p(X_n, F_n)` of `O_{Y,ȳ}`-modules. -/
def toCohomology [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] (p n : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    stalkModuleCat ybar (Modules.higherDirectImage f F p) ⟶
      (ModuleCat.restrictScalars
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n))).obj
        (cohomology f F ybar p n) :=
  stalkToPullbackGamma ybar (Modules.higherDirectImage f F p) ≫
    pullbackGammaToInf f F ybar p ≫ infToCohomology f F ybar p n

/-- The ideal power `m^n` annihilates the image of the geometric stalk in
`H^p(X_n, F_n)`, so it is contained in the kernel of `toCohomology`. -/
theorem pow_smul_le_ker_toCohomology [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] (p n : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n •
        (⊤ : Submodule (etaleLocalRing Y ybar)
          (stalkModuleCat ybar (Modules.higherDirectImage f F p))) ≤
      LinearMap.ker (toCohomology f F ybar p n).hom :=
  sorry

/-- The descended comparison
`(R^p f_* F)_ȳ / m^n (R^p f_* F)_ȳ ⟶ H^p(X_n, F_n)`. -/
def toCohomologyModPow [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] (p n : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    ModuleCat.of (etaleLocalRing Y ybar)
      (stalkModuleCat ybar (Modules.higherDirectImage f F p) ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n •
          (⊤ : Submodule (etaleLocalRing Y ybar)
            (stalkModuleCat ybar (Modules.higherDirectImage f F p)))) ⟶
      (ModuleCat.restrictScalars
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n))).obj
        (cohomology f F ybar p n) :=
  ConcreteCategory.ofHom
    ((IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n •
        (⊤ : Submodule (etaleLocalRing Y ybar)
          (stalkModuleCat ybar (Modules.higherDirectImage f F p)))).liftQ
      (toCohomology f F ybar p n).hom
      (pow_smul_le_ker_toCohomology f F ybar p n))

/-- The underlying function of the completed-stalk comparison at stage `n`. -/
private def toCompletedCohomologyFun [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] (p n : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
        (stalkModuleCat ybar (Modules.higherDirectImage f F p)) →
      completedCohomology f F ybar p n :=
  fun x ↦
    (toCohomologyModPow f F ybar p n).hom
      (AdicCompletion.eval (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
        (stalkModuleCat ybar (Modules.higherDirectImage f F p)) n x)

/-- The underlying function of the completed-stalk comparison is linear over
`O_{Y,ȳ}^∧`. -/
private theorem isLinearMap_toCompletedCohomologyFun [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] (p n : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    IsLinearMap
      (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
        (etaleLocalRing Y ybar))
      (toCompletedCohomologyFun f F ybar p n) :=
  sorry

/-- Evaluation of the completed stalk, followed by the stage comparison, as an
`O_{Y,ȳ}^∧`-linear map. -/
@[no_expose]
def toCompletedCohomology [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] (p n : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    ModuleCat.of
        (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (etaleLocalRing Y ybar))
        (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (stalkModuleCat ybar (Modules.higherDirectImage f F p))) ⟶
      completedCohomology f F ybar p n :=
  ConcreteCategory.ofHom
    (IsLinearMap.mk' (toCompletedCohomologyFun f F ybar p n)
      (isLinearMap_toCompletedCohomologyFun f F ybar p n))

/-- The induced map from the `m_ȳ`-adic completion of `(R^p f_* F)_ȳ` to the inverse
limit of `H^p(X_n, F_n)`, as `O_{Y,ȳ}^∧`-modules. -/
def limitComparison [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent]
    [Abelian X.Modules] [Abelian Y.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] (p : ℕ) :
    ModuleCat.of
        (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (etaleLocalRing Y ybar))
        (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
          (stalkModuleCat ybar (Modules.higherDirectImage f F p))) ⟶
      limit (system f F ybar p) :=
  limit.lift (system f F ybar p)
    { pt :=
        ModuleCat.of
          (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
            (etaleLocalRing Y ybar))
          (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
            (stalkModuleCat ybar (Modules.higherDirectImage f F p)))
      π :=
        { app := fun n ↦ toCompletedCohomology f F ybar p n.unop
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `limitComparison` to stage `n` is evaluation on the completion
followed by the stage comparison. -/
theorem limitComparison_comp_π [IsLocallyNoetherian Y] [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent]
    [Abelian X.Modules] [Abelian Y.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] (p n : ℕ) :
    limitComparison f F ybar p ≫ limit.π (system f F ybar p) (op n) =
      toCompletedCohomology f F ybar p n :=
  sorry

/-- For a proper morphism with locally Noetherian target and a coherent
quasi-coherent module, the canonical completed geometric-stalk comparison
is an isomorphism over the completed étale local ring. -/
@[stacks 08B1]
instance isIso_limitComparison [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] (ybar : GeometricPoint Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] (p : ℕ) :
    IsIso (limitComparison f F ybar p) :=
  sorry

end FormalFunctions
end AlgebraicGeometry.AlgebraicSpace
