/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.DegreewiseSplit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]

/- Remark 12.18.7 [0G6B] (1): totalization intertwines the first-direction shift with the
ordinary total-degree shift. -/
@[stacks 0G6B]
#check (HomologicalComplex₂.BidegreeShift.totalIso K 1 0).symm

variable {f g : K ⟶ L}

/- Remark 12.18.7 [0G6B] (2): a first-direction homotopy induces a homotopy between the
corresponding total maps. -/
@[stacks 0G6B]
#check HomologicalComplex₂.Total.Homotopy.First.of (c₁₂ := up ℤ)
  (f := f) (g := g)

/- The induced total maps are therefore equal in the homotopy category. -/
#check HomologicalComplex₂.Total.Homotopy.First.map_eq_in_homotopyCategory (c₁₂ := up ℤ)
  (f := f) (g := g)

variable (h : Homotopy f f)

/- Remark 12.18.7 [0G6B] (3): the induced self-homotopy agrees with the map to the
first-direction `(-1)`-shift under the canonical self-homotopy equivalence. -/
@[stacks 0G6B]
#check HomologicalComplex₂.Total.Homotopy.First.selfHomotopyToShift h

section DegreewiseSplit

variable [HasCountableCoproducts C]
variable (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))
variable (σ : ∀ p : ℤ,
  (S.map (eval (CochainComplex C ℤ) (up ℤ) p)).Splitting)

/- Remark 12.18.7 [0G6B] (4): the first-direction connecting map commutes with totalization and
the sign-free shift comparison. -/
@[stacks 0G6B]
#check HomologicalComplex₂.DegreewiseSplit.connectingHom_total₁ S σ

#check HomologicalComplex₂.DegreewiseSplit.splitting₁ S σ

end DegreewiseSplit
