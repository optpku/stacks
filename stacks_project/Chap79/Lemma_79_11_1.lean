/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.DenseOpenDescent
import StacksCheckRecall

/-!
# Descent of morphisms of algebraic spaces along a dense open

For morphisms `f : X ⟶ Y` and `g : X ⟶ Z` over `B`, with `Y` separated over
`B` and `g` surjective, flat, and locally of finite presentation, a factorization
of `f` over a scheme-theoretically dense open of `Z` extends through `g`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 79.11.1: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `f : X ⟶ Y` and `g : X ⟶ Z` be morphisms of algebraic spaces over `B`.
If `Y ↘ B` is separated, `g` is surjective, flat, and locally of finite
presentation, and `ι : V ⟶ Z` is a scheme-theoretically dense open immersion
such that `openInverseImageι g ι ≫ f` factors through `V`, then `f` factors
through `g`. -/
@[stacks 0AEL] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_desc_of_isSchemeTheoreticallyDense :
    ∀
    {S : Scheme.{u}} {B X Y Z V : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [OverClass Z B] [Separated (Y ↘ B)]
    {f : X ⟶ Y} {g : X ⟶ Z} [HomIsOver f B] [HomIsOver g B]
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (ι : V ⟶ Z) [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι]
    (hV : V ⟶ Y)
    (hV_fac : openInverseImageι g ι ≫ f = openInverseImageTo g ι ≫ hV),
    ∃ h : Z ⟶ Y, HomIsOver h B ∧ g ≫ h = f)

end AlgebraicGeometry.AlgebraicSpace
