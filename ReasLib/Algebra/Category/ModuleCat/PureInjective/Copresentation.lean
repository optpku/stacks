/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Evaluation
public import ReasLib.Algebra.Category.ModuleCat.Pure

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]

/-- The character dual of every `R`-module is pure injective. -/
theorem CharacterModule.moduleObj_pureInjective (M : ModuleCat.{v} R) :
    (CharacterModule.moduleObj R M).PureInjective := sorry

/-- An `R`-module is pure injective if and only if its canonical map to its
double character dual is a split monomorphism. -/
theorem ModuleCat.pureInjective_iff_isSplitMono_evaluationApp
    (I : ModuleCat.{v} R) :
    I.PureInjective ↔ IsSplitMono (CharacterModule.evaluationApp R I) := sorry

/-- Every `R`-module is the first term of a universally exact short complex
whose middle term is pure injective. -/
theorem ModuleCat.exists_universallyExact_pureInjective_copresentation
    (M : ModuleCat.{v} R) :
    ∃ (I N : ModuleCat.{v} R) (f : M ⟶ I) (g : I ⟶ N)
      (hzero : f ≫ g = 0),
      (ShortComplex.mk f g hzero).UniversallyExact ∧ I.PureInjective := sorry
