/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u v

/- Lemma 80.11.1: an fppf sheaf is an algebraic space if its localizations along
an fppf covering are algebraic spaces and their coproduct in fppf sheaves exists
and is an algebraic space. -/
@[stacks 04SK] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_fppfLocal :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {I : Type v} (Si : I → Over S) (hSi : Scheme.FppfCovering Si)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F))
    [HasCoproduct (fppfLocalizationSheaf Si hFi)]
    (hcoprod : IsAlgebraicSpace (∐ (fppfLocalizationSheaf Si hFi)).obj),
    IsAlgebraicSpace F)
