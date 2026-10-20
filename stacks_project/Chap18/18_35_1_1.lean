/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {A B A' B' : Sheaf J CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
variable (sq : CommSq ρ α β φ)

/- Equation 18.35.1.1 (08TX): a commutative square of ring sheaves induces the canonical map
between their naive cotangent complexes. -/
@[stacks 08TX]
#check (map sq :
  (extendComplex φ).obj (obj A (Under.mk α)) ⟶
    obj A' (Under.mk β))

/- The reusable owner also records functorial composition of the canonical maps. -/
#check @map_comp

end SheafOfModules.RingedSite.NaiveCotangent
