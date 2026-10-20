/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Finite
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Flat
public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
public import ReasLib.RingTheory.Pullback.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative module pullbacks after ring base change

This leaf specializes the canonical module pullback adjunction to a fibre-product base-change
situation. It owns the source-specific counit, finite, flat, and finite-presentation interfaces;
the underlying right adjoint and adjunction remain the canonical `ModuleCat.Pullback` data.

@stack 08KM
@stack 08IH
@stack 07RW
@stack 08KP
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace FiberProductBaseChangeSituation

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- Lemma 15.7.2: the fibre-product module right adjoint in a base-change situation. -/
@[stacks 08KM "relative fibre-product right adjoint"]
noncomputable abbrev relativeRightAdjoint (S : Situation) :
    S.relativeModuleCategory ⥤ ModuleCat Dp :=
  ModuleCat.Pullback.rightAdjoint
    S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes

/-- Lemma 15.7.2: relative module base change is left adjoint to the fibre-product module
functor. -/
@[stacks 08KM "relative fibre-product adjunction"]
noncomputable abbrev relativeAdjunction (S : Situation) :
    S.relativeModuleFunctor ⊣ relativeRightAdjoint S :=
  ModuleCat.Pullback.adjunction
    S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes

/-- Lemma 15.7.2: the counit of the relative fibre-product adjunction is an isomorphism. -/
@[stacks 08KM "relative adjunction counit is an isomorphism"]
theorem relativeCounit_isIso (S : Situation) :
    IsIso (relativeAdjunction S).counit := sorry

/-- The natural counit isomorphism for relative fibre-product modules. -/
@[stacks 08KM "relative fibre-product counit isomorphism"]
noncomputable def relativeCounitIso (S : Situation) :
    relativeRightAdjoint S ⋙ S.relativeModuleFunctor ≅ 𝟭 S.relativeModuleCategory :=
  -- Local instance justification (proof-local temporary data): `asIso` consumes the separately
  -- stated invertibility proposition without registering a global choice.
  letI : IsIso (relativeAdjunction S).counit := relativeCounit_isIso S
  asIso (relativeAdjunction S).counit

/-- Lemma 15.7.4: finite components have a finite relative fibre-product module. -/
@[stacks 08IH "finite relative fibre-product module"]
theorem relativeRightAdjoint_finite
    (S : Situation) (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst) (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite Dp ((relativeRightAdjoint S).obj X) := sorry

namespace RelativeFlat

/-- The property of a `D'`-module being flat after restriction to the pullback base ring `B'`. -/
@[stacks 07RW "D'-modules flat over B'"]
def moduleProperty (S : Situation) : ObjectProperty (ModuleCat Dp) :=
  fun L ↦ Module.Flat S.Bprime ((ModuleCat.restrictScalars S.bprimeToDp).obj L)

/-- The full subcategory of `D'`-modules that are flat over `B'`. -/
@[stacks 07RW "category of D'-modules flat over B'"]
abbrev ModuleCategory (S : Situation) := (moduleProperty S).FullSubcategory

/-- The property of a relative pullback triple whose components are flat over `B` and `A'`. -/
@[stacks 07RW "componentwise relative flatness"]
def pullbackProperty (S : Situation) : ObjectProperty S.relativeModuleCategory :=
  fun X ↦
    Module.Flat B ((ModuleCat.restrictScalars S.bToD).obj X.fst) ∧
      Module.Flat A' ((ModuleCat.restrictScalars S.aprimeToCPrime).obj X.snd)

/-- The full subcategory of relative pullback triples with flat components. -/
@[stacks 07RW "relative flat pullback category"]
abbrev PullbackCategory (S : Situation) := (pullbackProperty S).FullSubcategory

/-- Relative base change sends a module flat over `B'` to a pullback triple with flat
components. -/
@[stacks 07RW "relative base change preserves componentwise flatness"]
theorem baseChange_mem (S : Situation) (L : ModuleCategory S) :
    pullbackProperty S (S.relativeModuleFunctor.obj L.obj) := sorry

/-- Relative module base change restricted to the flat full subcategories. -/
@[stacks 07RW "relative flat base-change functor"]
def baseChangeFunctor (S : Situation) : ModuleCategory S ⥤ PullbackCategory S :=
  (pullbackProperty S).lift
    ((moduleProperty S).ι ⋙ S.relativeModuleFunctor) (baseChange_mem S)

/-- Lemma 15.7.5 (1): the fibre-product module of a triple with flat components is flat over
`B'`. -/
@[stacks 07RW "(1), relative fibre-product flatness"]
theorem rightAdjoint_mem (S : Situation) (X : S.relativeModuleCategory)
    (hX : pullbackProperty S X) :
    moduleProperty S ((relativeRightAdjoint S).obj X) := sorry

/-- The relative fibre-product functor with source restricted to componentwise flat triples. -/
@[stacks 07RW "relative fibre-product functor on flat triples"]
def rightAdjointOnPullback (S : Situation) : PullbackCategory S ⥤ ModuleCat Dp :=
  (pullbackProperty S).ι ⋙ relativeRightAdjoint S

/-- Membership of the relative fibre-product of an object in the flat pullback category. -/
@[stacks 07RW "relative flat fibre-product membership"]
theorem rightAdjointOnPullback_mem (S : Situation) (X : PullbackCategory S) :
    moduleProperty S ((rightAdjointOnPullback S).obj X) := sorry

/-- The relative fibre-product right adjoint restricted to the flat full subcategories. -/
@[stacks 07RW "relative flat fibre-product functor"]
def rightAdjointFunctor (S : Situation) : PullbackCategory S ⥤ ModuleCategory S :=
  (moduleProperty S).lift (rightAdjointOnPullback S) (rightAdjointOnPullback_mem S)

/-- Lemma 15.7.5 (2): a module flat over `B'` is reconstructed by the unit of the relative
fibre-product adjunction. -/
@[stacks 07RW "(2), relative flat module reconstruction"]
theorem unit_isIso (S : Situation) (L : ModuleCat Dp) (hL : moduleProperty S L) :
    IsIso ((relativeAdjunction S).unit.app L) := sorry

/-- Lemma 15.7.5 (3): relative base change is an equivalence on the flat full subcategories. -/
@[stacks 07RW "(3), relative equivalence on flat modules"]
theorem baseChangeFunctor_isEquivalence (S : Situation) :
    Functor.IsEquivalence (baseChangeFunctor S) := sorry

end RelativeFlat

/-- Lemma 15.7.6: finite presentation of the relative fibre-product module under a flat then
finitely-presented factorization of `B' → D'`. -/
@[stacks 08KP]
theorem relativeRightAdjoint_finitePresentation_of_factorization
    (S : Situation) (X : S.relativeModuleCategory)
    [Module.FinitePresentation S.D X.fst]
    [Module.Flat B ((ModuleCat.restrictScalars S.bToD).obj X.fst)]
    [Module.FinitePresentation S.CPrime X.snd]
    [Module.Flat A' ((ModuleCat.restrictScalars S.aprimeToCPrime).obj X.snd)]
    (hfactor :
      ∃ (P : Type u) (_ : CommRing P) (g : S.Bprime →+* P) (h : P →+* Dp),
        g.Flat ∧ h.FinitePresentation ∧ S.bprimeToDp = h.comp g) :
    Module.FinitePresentation Dp ((relativeRightAdjoint S).obj X) := sorry

end FiberProductBaseChangeSituation
