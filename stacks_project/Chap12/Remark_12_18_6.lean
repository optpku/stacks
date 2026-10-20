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

/- Remark 12.18.6 [0G6A] (1): totalization intertwines the second-direction shift with the
ordinary total-degree shift. -/
@[stacks 0G6A]
#check (HomologicalComplex₂.BidegreeShift.totalIso K 0 1).symm

variable {f g : K ⟶ L}

/- Remark 12.18.6 [0G6A] (2): a homotopy after flipping the two directions induces a homotopy
between the corresponding total maps. -/
@[stacks 0G6A]
#check HomologicalComplex₂.Total.Homotopy.Second.of (K := K) (L := L) (f := f) (g := g)

/- The induced total maps are therefore equal in the homotopy category. -/
#check HomologicalComplex₂.Total.Homotopy.Second.map_eq_in_homotopyCategory
  (K := K) (L := L) (f := f) (g := g)

#check @HomologicalComplex₂.Total.Homotopy.Second.FromFlipToShift.componentOf

variable (h : Homotopy ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)
  ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f))

/- Remark 12.18.6 [0G6A] (3): the induced self-homotopy agrees with the map to the
second-direction `(-1)`-shift under the canonical self-homotopy equivalence. -/
@[stacks 0G6A]
#check HomologicalComplex₂.Total.Homotopy.Second.selfHomotopyToShift h

section DegreewiseSplit

variable [HasCountableCoproducts C]
variable (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))
variable (σ : ∀ q : ℤ,
  (S.map ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)) ⋙
    eval (CochainComplex C ℤ) (up ℤ) q)).Splitting)

/- Remark 12.18.6 [0G6A] (4): the second-direction connecting map commutes with totalization
and the Koszul-signed shift comparison. -/
@[stacks 0G6A]
#check HomologicalComplex₂.DegreewiseSplit.connectingHom_total₂ S σ

#check HomologicalComplex₂.DegreewiseSplit.splitting₂ S σ

end DegreewiseSplit
