/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Sites.Proetale.Derived.Sections
import StacksCheckRecall

/-!
# Lemma 61.14.3

On a quasi-compact quasi-separated scheme, derived global sections on the small
pro-étale site commute with those direct sums that exist in `D⁺` and with sequential
homotopy colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) (ProEt.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]

/- Lemma 61.14.3 (direct sums): derived global sections preserve coproducts
that exist in the bounded-below derived category. -/
@[stacks 09A3] #check
  (AlgebraicGeometry.Scheme.ProEt.rGamma_preservesCoproduct :
    ∀ {I : Type w} (E : I → DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u}))
      [HasCoproduct E],
      PreservesColimit (Discrete.functor E) (globalSectionsPlusDerived X))

/- Lemma 61.14.3 (homotopy colimits): derived global sections preserve
existing sequential homotopy colimits in the bounded-below derived category. -/
@[stacks 09A3] #check
  (AlgebraicGeometry.Scheme.ProEt.rGamma_preservesHomotopyColimit :
    ∀ (K : ℕ ⥤ DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u}))
      {E : DerivedCategory.Plus (Sheaf (topology X) AddCommGrpCat.{u})},
      HomotopyColimit.IsOf K E →
        HomotopyColimit.IsOf (K ⋙ globalSectionsPlusDerived X)
          ((globalSectionsPlusDerived X).obj E))

end AlgebraicGeometry.Scheme.ProEt

end
