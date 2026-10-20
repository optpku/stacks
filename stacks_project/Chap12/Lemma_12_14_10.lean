/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex (CochainComplex C ℤ))
variable (σ : ∀ n : ℤ, (S.degreewise n).Splitting) (n : ℤ)

/- Lemma 12.14.10: a degreewise splitting of a short complex of cochain complexes determines
the canonical connecting map `S.X₃ ⟶ S.X₁⟦1⟧`. -/
@[stacks 011J]
#check (CochainComplex.homOfDegreewiseSplit S σ :
  S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧)

/- Its component formula is already part of the mathlib owner API. -/
#check (CochainComplex.homOfDegreewiseSplit_f S σ n :
  (CochainComplex.homOfDegreewiseSplit S σ).f n =
    (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v n (n + 1) rfl)

/- ReasLib exposes the same component as direct data, together with its bridge to the canonical
connecting map. -/
#check (CochainComplex.homOfDegreewiseSplit.coordinate S σ n :
  S.X₃.X n ⟶ S.X₁.X (n + 1))
#check (CochainComplex.homOfDegreewiseSplit.component S σ n :
  S.X₃.X n ⟶ (S.X₁⟦(1 : ℤ)⟧).X n)

#check (CochainComplex.homOfDegreewiseSplit.component_comp_xIso S σ n :
  CochainComplex.homOfDegreewiseSplit.component S σ n ≫
      (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
    CochainComplex.homOfDegreewiseSplit.coordinate S σ n)

#check (CochainComplex.homOfDegreewiseSplit.component_eq S σ n :
  (CochainComplex.homOfDegreewiseSplit S σ).f n =
    CochainComplex.homOfDegreewiseSplit.component S σ n)
