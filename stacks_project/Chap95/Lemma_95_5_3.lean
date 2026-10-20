/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.QCohStack.FiniteType.Small

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 95.5.3: there exists a subcategory `QCoh_fg,small ⊂ QCoh_fg` whose inclusion
functor `P.ι : QCoh_fg,small ⟶ QCoh_fg` is fully faithful (the canonical `Full`/`Faithful`
instances) and essentially surjective, and whose restricted projection
`p_fg,small = P.ι ⋙ (stack S).p` turns `QCoh_fg,small` into a stack over `(Sch/S)_fppf`.
Fiberwise `Small.{u}` is the big-site meaning of `fg,small`, since the ambient fibre is
only `EssentiallySmall.{u}`. -/
@[stacks 04U6] #check
  (AlgebraicGeometry.QCohStack.FG.exists_smallSubcategory :
    ∀ S : AlgebraicGeometry.Scheme.{u},
    ∃ P : CategoryTheory.ObjectProperty (AlgebraicGeometry.QCohStack.FG.stack S).total,
      P.ι.EssSurj ∧
        CategoryTheory.IsStack.OnSite (AlgebraicGeometry.Scheme.fppfTopology.over S)
          (P.ι ⋙ (AlgebraicGeometry.QCohStack.FG.stack S).p) ∧
        ∀ U : CategoryTheory.Over S,
          Small.{u} ((P.ι ⋙ (AlgebraicGeometry.QCohStack.FG.stack S).p).Fiber U))

/- Remark 8.4.9 condition (4): the fibre of `p_fg` over `U` is essentially small. -/
#check
  (AlgebraicGeometry.QCohStack.FG.fibers_essentiallySmall :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (U : CategoryTheory.Over S),
      CategoryTheory.ObjectProperty.EssentiallySmall.{u}
        (⊤ : CategoryTheory.ObjectProperty ((AlgebraicGeometry.QCohStack.FG.p S).Fiber U)))

