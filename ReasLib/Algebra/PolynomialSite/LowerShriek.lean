/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.Terminal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Lower shriek on a polynomial algebra

The colimit functor on presheaves on the opposite polynomial site is exact and
naturally isomorphic to evaluation at the identity augmentation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsPolynomial A B]

variable (𝒜 : Type v) [Category.{w} 𝒜] [Abelian 𝒜]
  [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ 𝒜]

/-- For a polynomial `A`-algebra `B`, the colimit functor on presheaves on
`PolynomialSite A B` is naturally isomorphic to evaluation at the identity augmentation. -/
def lowerShriekIsoEval :
    (colim : ((PolynomialSite A B)ᵒᵖ ⥤ 𝒜) ⥤ 𝒜) ≅
      (evaluation ((PolynomialSite A B)ᵒᵖ) 𝒜).obj (evalObj A B) :=
  NatIso.ofComponents
    (fun F ↦ (colimit.isColimit F).coconePointUniqueUpToIso
      (colimitOfDiagramTerminal (evalObj_isTerminal A B) F))
    (fun {_ _} _ ↦ sorry)

/-- For a polynomial `A`-algebra `B`, the colimit functor on presheaves on
`PolynomialSite A B` with abelian coefficients is exact. -/
theorem lowerShriek_exact :
    exactFunctor ((PolynomialSite A B)ᵒᵖ ⥤ 𝒜) 𝒜
      (colim : ((PolynomialSite A B)ᵒᵖ ⥤ 𝒜) ⥤ 𝒜) :=
  sorry

/-- The evaluation isomorphism at a presheaf is the canonical comparison from its
colimit to the colimit cocone at the terminal identity augmentation. -/
theorem lowerShriekIsoEval_app (F : (PolynomialSite A B)ᵒᵖ ⥤ 𝒜) :
    (lowerShriekIsoEval A B 𝒜).app F =
      (colimit.isColimit F).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal (evalObj_isTerminal A B) F) :=
  sorry

end Algebra.PolynomialSite
