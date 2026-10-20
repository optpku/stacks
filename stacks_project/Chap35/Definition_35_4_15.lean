/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.BaseExtension
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Definition 35.4.15 (1): the canonical functor from `R`-modules to descent data
along `f : R →+* S` is called base extension along `f`. -/
@[stacks 08WY] #check (ModuleCat.baseExtension :
  ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S),
    ModuleCat.{u} R ⥤ ModuleCat.DescentData f)

/- Definition 35.4.15 (2): a ring homomorphism is a descent morphism for modules when
base extension is fully faithful. -/
@[stacks 08WY] #check (RingHom.descentForModules_iff :
  ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S),
    f.DescentForModules ↔ Nonempty (ModuleCat.baseExtension f).FullyFaithful)

/- Definition 35.4.15 (3): a ring homomorphism is an effective descent morphism for modules
when base extension is an equivalence of categories. -/
@[stacks 08WY] #check (RingHom.effectiveDescentForModules_iff :
  ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S),
    f.EffectiveDescentForModules ↔ (ModuleCat.baseExtension f).IsEquivalence)
