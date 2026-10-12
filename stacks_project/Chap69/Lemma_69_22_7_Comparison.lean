/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.GlobalSections
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap69.Lemma_69_20_4_GradedCohomology
public import stacks_project.Chap69.Lemma_69_22_7_Neighbourhood

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
  GradedCohomology.cohomologyOver (quotientToSpec ybar n ≫ specHom ybar)
    (toSpec f ybar n) (sheaf f F ybar n) p

/-- `cohomology f F ybar p n` is affine-base cohomology of `F_n` on `X_n`. -/
theorem cohomology_eq [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (thickening ybar n).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules] :
    cohomology f F ybar p n =
      GradedCohomology.cohomologyOver (quotientToSpec ybar n ≫ specHom ybar)
        (toSpec f ybar n) (sheaf f F ybar n) p :=
  rfl

/-- Pullback of `F` along `spaceStep ≫ i_{n+1}` recovers `F_n`. -/
theorem sheaf_spaceStep_comp [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (spaceStep f ybar n ≫ toX f ybar (n + 1))).obj F =
      sheaf f F ybar n :=
  sorry

/-- Identification `F_n ≅ spaceStep^* F_{n+1}` from `i_n = spaceStep ≫ i_{n+1}`. -/
def sheafStepPullback [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (spaceStep f ybar n)).obj (sheaf f F ybar (n + 1)) ⟶
      sheaf f F ybar n :=
  (pullbackCompIso (spaceStep f ybar n) (toX f ybar (n + 1))).hom.app F ≫
    eqToHom
      (congrArg (fun i ↦ (Modules.pullback i).obj F)
        (pullback.lift_fst (toX f ybar n)
          (toSpec f ybar n ≫ thickeningStep ybar n)
          (spaceStep_condition f ybar n)))

/-- Adjunction unit `F_{n+1} ⟶ spaceStep_* F_n`. -/
def sheafUnit [IsLocallyNoetherian Y] (n : ℕ) :
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

/-- Pushforward along an infinitesimal neighbourhood transition preserves injective objects. -/
instance instPreservesInjectiveObjects_pushforward_spaceStep [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules] :
    (pushforward (spaceStep f ybar n)).PreservesInjectiveObjects :=
  sorry

/-- Pushforward along a thickening transition preserves homology. -/
instance instPreservesHomology_pushforward_thickeningStep [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules] :
    (pushforward (thickeningStep ybar n)).PreservesHomology :=
  sorry

/-- Leray comparison of higher direct images along `spaceStep` and `thickeningStep`. -/
def higherDirectImagePushforward [IsLocallyNoetherian Y] (p n : ℕ)
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
  (Functor.RightDerived.precompObjIso (pushforward (spaceStep f ybar n))
      (pushforward (toSpec f ybar (n + 1))) p (sheaf f F ybar n)).inv ≫
    (NatIso.rightDerived
        (pushforwardComp (spaceStep f ybar n) (toSpec f ybar (n + 1))) p).hom.app
      (sheaf f F ybar n) ≫
    (NatIso.rightDerived
        (eqToIso (congrArg pushforward
          (pullback.lift_snd (toX f ybar n)
            (toSpec f ybar n ≫ thickeningStep ybar n)
            (spaceStep_condition f ybar n)))) p).hom.app
      (sheaf f F ybar n) ≫
    (NatIso.rightDerived
        (pushforwardComp (toSpec f ybar n) (thickeningStep ybar n)).symm p).hom.app
      (sheaf f F ybar n) ≫
    (Functor.RightDerived.postcompObjIso (pushforward (toSpec f ybar n))
        (pushforward (thickeningStep ybar n)) p (sheaf f F ybar n)).hom

/-- After pushing `F_n` forward along `spaceStep`, affine-base cohomology maps to
restriction of scalars of `H^p(X_n, F_n)`. -/
def cohomologyOverPushforward [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (space f ybar (n + 1)).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (thickening ybar (n + 1)).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (space f ybar (n + 1)).Modules] :
    GradedCohomology.cohomologyOver (quotientToSpec ybar (n + 1) ≫ specHom ybar)
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
  GradedCohomology.cohomologyOverMap
      (quotientToSpec ybar (n + 1) ≫ specHom ybar) (toSpec f ybar (n + 1))
      (sheafUnit f F ybar n) p ≫
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

/-- Affine-base neighbourhood cohomology is an `O_{Y,ȳ}^∧`-module via its `ModuleCat`
carrier. -/
instance module_completedCohomology [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (thickening ybar n).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules] :
    Module
      (AdicCompletion (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar))
        (etaleLocalRing Y ybar))
      (completedCohomology f F ybar p n) :=
  ModuleCat.isModule (completedCohomology f F ybar p n)

/-- Affine-base neighbourhood cohomology is an abelian group via its `ModuleCat`
carrier. -/
instance addCommGroup_completedCohomology [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (thickening ybar n).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules] :
    AddCommGroup (completedCohomology f F ybar p n) :=
  ModuleCat.isAddCommGroup (completedCohomology f F ybar p n)

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
def completedCohomologySeq [IsLocallyNoetherian Y]
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
def cohomologyStepSeq [IsLocallyNoetherian Y]
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
  Functor.ofOpSequence (cohomologyStepSeq f F ybar p)

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
  GradedCohomology.cohomologyOver (specHom ybar) (toSpecInf f ybar)
    (sheafInf f F ybar) p

/-- Pullback of `F` along `toInf ≫ i_∞` recovers `F_n`. -/
theorem sheaf_toInf_comp [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (toInf f ybar n ≫ toXInf f ybar)).obj F =
      sheaf f F ybar n :=
  sorry

/-- Identification `F_n ≅ toInf^* F_∞` from `i_n = toInf ≫ i_∞`. -/
def sheafInfPullback [IsLocallyNoetherian Y] (n : ℕ) :
    (Modules.pullback (toInf f ybar n)).obj (sheafInf f F ybar) ⟶
      sheaf f F ybar n :=
  (pullbackCompIso (toInf f ybar n) (toXInf f ybar)).hom.app F ≫
    eqToHom
      (congrArg (fun i ↦ (Modules.pullback i).obj F)
        (pullback.lift_fst (toX f ybar n)
          (toSpec f ybar n ≫ toSpecSpace ybar n)
          (toInf_condition f ybar n)))

/-- Adjunction unit `F_∞ ⟶ toInf_* F_n`. -/
def sheafInfUnit [IsLocallyNoetherian Y] (n : ℕ) :
    sheafInf f F ybar ⟶ (pushforward (toInf f ybar n)).obj (sheaf f F ybar n) :=
  (pullbackPushforwardAdjunction (toInf f ybar n)).unit.app (sheafInf f F ybar) ≫
    (pushforward (toInf f ybar n)).map (sheafInfPullback f F ybar n)

/-- Pushforward along `X_n ⟶ X_∞` preserves homology. -/
instance instPreservesHomology_pushforward_toInf [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules] :
    (pushforward (toInf f ybar n)).PreservesHomology :=
  sorry

/-- Pushforward along `X_n ⟶ X_∞` preserves injective objects. -/
instance instPreservesInjectiveObjects_pushforward_toInf [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules] :
    (pushforward (toInf f ybar n)).PreservesInjectiveObjects :=
  sorry

/-- Pushforward along `Spec(O/m^n) ⟶ Spec(O)` preserves homology. -/
instance instPreservesHomology_pushforward_toSpecSpace [IsLocallyNoetherian Y] (n : ℕ)
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules] :
    (pushforward (toSpecSpace ybar n)).PreservesHomology :=
  sorry

/-- Leray comparison of higher direct images along `toInf` and `toSpecSpace`. -/
def higherDirectImageInfPushforward [IsLocallyNoetherian Y] (p n : ℕ)
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
  (Functor.RightDerived.precompObjIso (pushforward (toInf f ybar n))
      (pushforward (toSpecInf f ybar)) p (sheaf f F ybar n)).inv ≫
    (NatIso.rightDerived
        (pushforwardComp (toInf f ybar n) (toSpecInf f ybar)) p).hom.app
      (sheaf f F ybar n) ≫
    (NatIso.rightDerived
        (eqToIso (congrArg pushforward
          (pullback.lift_snd (toX f ybar n)
            (toSpec f ybar n ≫ toSpecSpace ybar n)
            (toInf_condition f ybar n)))) p).hom.app
      (sheaf f F ybar n) ≫
    (NatIso.rightDerived
        (pushforwardComp (toSpec f ybar n) (toSpecSpace ybar n)).symm p).hom.app
      (sheaf f F ybar n) ≫
    (Functor.RightDerived.postcompObjIso (pushforward (toSpec f ybar n))
        (pushforward (toSpecSpace ybar n)) p (sheaf f F ybar n)).hom

/-- After pushing `F_n` forward along `toInf`, affine-base cohomology maps to
restriction of scalars of `H^p(X_n, F_n)`. -/
def cohomologyOverInfPushforward [IsLocallyNoetherian Y] (p n : ℕ)
    [Abelian X.Modules]
    [Abelian (space f ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (thickening ybar n).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] :
    GradedCohomology.cohomologyOver (specHom ybar) (toSpecInf f ybar)
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
  GradedCohomology.cohomologyOverMap (specHom ybar) (toSpecInf f ybar)
      (sheafInfUnit f F ybar n) p ≫
    cohomologyOverInfPushforward f F ybar p n

/-- Global sections of `c^* G` on `Spec(O_{Y,ȳ})`. -/
def pullbackGamma (ybar : GeometricPoint Y) (G : Y.Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    ModuleCat (etaleLocalRing Y ybar) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).obj
    ((toScheme (Over.mk (specHom ybar))).obj
      ((Modules.pullback (fromSpecEtaleLocalRing ybar)).obj G))

/-- The geometric stalk of `R^p f_* F` is an `O_{Y,ȳ}`-module via its `ModuleCat`
carrier. -/
instance module_stalk [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    Module (etaleLocalRing Y ybar)
      (stalkModuleCat ybar (Modules.higherDirectImage f F p)) :=
  ModuleCat.isModule (stalkModuleCat ybar (Modules.higherDirectImage f F p))

/-- The geometric stalk of `R^p f_* F` is an abelian group via its `ModuleCat`
carrier. -/
instance addCommGroup_stalk [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    AddCommGroup (stalkModuleCat ybar (Modules.higherDirectImage f F p)) :=
  ModuleCat.isAddCommGroup (stalkModuleCat ybar (Modules.higherDirectImage f F p))

/-- Global sections of `c_* M` on `Y`, after applying `toScheme` on `Spec(O_{Y,ȳ})`. -/
def pushforwardGamma (ybar : GeometricPoint Y) (M : (specSpace ybar).Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    ModuleCat (etaleLocalRing Y ybar) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).obj
    ((toScheme (Over.mk (specHom ybar))).obj M)

/-- The scheme morphism `Spec(O_{Y,ȳ}) ⟶ N` through the Zariski stalk of an étale
neighbourhood of `ȳ`. -/
def neighborhoodFromSpec (ybar : GeometricPoint Y) (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (etaleLocalRing Y ybar)) ⟶ N.scheme :=
  Spec.map (CommRingCat.ofHom (etaleLocalRing_etaleNeighborhood.fromZariskiStalk N)) ≫
    N.scheme.fromSpecStalk N.center

/-- The scheme module on an étale neighbourhood of `Y` obtained by restricting `G`. -/
def neighborhoodSchemeModule {Y : AlgebraicSpace S} (G : Y.Modules)
    (U : smallEtaleSite Y) : U.left.left.Modules :=
  (toScheme U.left).obj ((Modules.pullback U.hom).obj G)

/-- Global sections of the adjunction counit, as a map `Γ(c^* c_* M) ⟶ Γ(M)`. -/
def stalkPushforwardToGamma (ybar : GeometricPoint Y) (M : (specSpace ybar).Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    pullbackGamma ybar ((pushforward (fromSpecEtaleLocalRing ybar)).obj M) ⟶
      pushforwardGamma ybar M :=
  (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).map
    ((toScheme (Over.mk (specHom ybar))).map
      ((pullbackPushforwardAdjunction (fromSpecEtaleLocalRing ybar)).counit.app M))

/-- `stalkPushforwardToGamma` is `moduleSpecΓFunctor` of `toScheme` of the adjunction counit. -/
theorem stalkPushforwardToGamma_eq (ybar : GeometricPoint Y)
    (M : (specSpace ybar).Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    stalkPushforwardToGamma ybar M =
      (moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing Y ybar))).map
        ((toScheme (Over.mk (specHom ybar))).map
          ((pullbackPushforwardAdjunction (fromSpecEtaleLocalRing ybar)).counit.app M)) :=
  rfl

/-- Étale-site sections of `G` on `U` identify with Zariski global sections of the restricted
scheme module. -/
theorem presheafObj_eq_neighborhoodGamma {Y : AlgebraicSpace S} (G : Y.Modules)
    (U : smallEtaleSite Y) :
    G.val.presheaf.obj (op U) =
      (Scheme.Modules.presheaf (neighborhoodSchemeModule G U)).obj
        (op (⊤ : U.left.left.Opens)) :=
  sorry

/-- Global sections of `f_* f^* (G|_U)` on an étale neighbourhood identify with `Γ(c^* G)`. -/
theorem neighborhoodPushforwardGamma_eq (ybar : GeometricPoint Y) (G : Y.Modules)
    (U : smallEtaleSite Y) (l : OverLift ybar U)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    (Scheme.Modules.presheaf
        ((Scheme.Modules.pushforward
            (neighborhoodFromSpec ybar (SmallEtaleNeighborhood.of U l.hom l.fac))).obj
          ((Scheme.Modules.pullback
              (neighborhoodFromSpec ybar (SmallEtaleNeighborhood.of U l.hom l.fac))).obj
            (neighborhoodSchemeModule G U)))).obj
      (op (⊤ : U.left.left.Opens)) =
      (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (pullbackGamma ybar G) :=
  sorry

/-- The additive comparison from sections of `G` on an étale neighbourhood of `ȳ` to
`Γ(c^* G)`. -/
def stalkToPullbackGammaComponent (ybar : GeometricPoint Y) (G : Y.Modules)
    (U : smallEtaleSite Y) (l : OverLift ybar U)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    G.val.presheaf.obj (op U) ⟶
      (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (pullbackGamma ybar G) :=
  eqToHom (presheafObj_eq_neighborhoodGamma G U) ≫
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction
          (neighborhoodFromSpec ybar (SmallEtaleNeighborhood.of U l.hom l.fac))).unit.app
        (neighborhoodSchemeModule G U))
      (⊤ : U.left.left.Opens) ≫
    eqToHom (neighborhoodPushforwardGamma_eq ybar G U l)

/-- Neighbourhood-section comparisons are natural in morphisms of the small étale site. -/
theorem stalkToPullbackGammaComponent_w (ybar : GeometricPoint Y) (G : Y.Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules]
    {U V : smallEtaleSite Y} (g : U ⟶ V) (l : OverLift ybar U) :
    G.val.presheaf.map g.op ≫ stalkToPullbackGammaComponent ybar G U l =
      stalkToPullbackGammaComponent ybar G V (OverLift.map g l) :=
  sorry

/-- Additive comparison from the étale stalk of `G` to global sections of `c^* G`. -/
def stalkToPullbackGammaAdd (ybar : GeometricPoint Y) (G : Y.Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    (toSmallEtalePoint ybar).presheafFiber.obj G.val.presheaf ⟶
      (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (pullbackGamma ybar G) :=
  (toSmallEtalePoint ybar).presheafFiberDesc
    (fun U l ↦ stalkToPullbackGammaComponent ybar G U l)
    (fun {U V} g l ↦ stalkToPullbackGammaComponent_w (U := U) (V := V) ybar G g l)

/-- The additive group of an étale module stalk is the site-point fibre of the underlying
additive presheaf. -/
theorem stalkModuleCat_presheafFiber_eq (ybar : GeometricPoint Y) (G : Y.Modules) :
    (forget₂ (ModuleCat (etaleLocalRing Y ybar)) AddCommGrpCat).obj
        (stalkModuleCat ybar G) =
      (toSmallEtalePoint ybar).presheafFiber.obj G.val.presheaf :=
  sorry

/-- The underlying function of the comparison `(R-module stalk) ⟶ Γ(c^* G)`. -/
def stalkToPullbackGammaFun (ybar : GeometricPoint Y) (G : Y.Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    stalkModuleCat ybar G → pullbackGamma ybar G :=
  fun x ↦
    (eqToHom (stalkModuleCat_presheafFiber_eq ybar G) ≫
      stalkToPullbackGammaAdd ybar G).hom x

/-- The underlying function of `stalkToPullbackGamma` is linear over `O_{Y,ȳ}`. -/
theorem isLinearMap_stalkToPullbackGammaFun (ybar : GeometricPoint Y) (G : Y.Modules)
    [Abelian Y.Modules] [Abelian (specSpace ybar).Modules] :
    IsLinearMap (etaleLocalRing Y ybar) (stalkToPullbackGammaFun ybar G) :=
  sorry

/-- Comparison from the étale stalk of `G` to global sections of `c^* G`. -/
def stalkToPullbackGamma (ybar : GeometricPoint Y) (G : Y.Modules)
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
def toCohomology [IsLocallyNoetherian Y] (p n : ℕ)
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
theorem pow_smul_le_ker_toCohomology [IsLocallyNoetherian Y] (p n : ℕ)
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
def toCohomologyModPow [IsLocallyNoetherian Y] (p n : ℕ)
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
def toCompletedCohomologyFun [IsLocallyNoetherian Y] (p n : ℕ)
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
theorem isLinearMap_toCompletedCohomologyFun [IsLocallyNoetherian Y] (p n : ℕ)
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
def toCompletedCohomology [IsLocallyNoetherian Y] (p n : ℕ)
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
def limitComparison [IsLocallyNoetherian Y]
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
theorem limitComparison_comp_π [IsLocallyNoetherian Y]
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

end FormalFunctions
end AlgebraicGeometry.AlgebraicSpace
