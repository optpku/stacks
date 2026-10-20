/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.LocallyOfFinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 32.10.5 compatibility entry point

The quasi-compact, quasi-separated locally finite-presentation over-category
and its directed-limit descent API are owned by
`ReasLib.AlgebraicGeometry.Scheme.Limit.LocallyOfFinitePresentation`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 32.10.5. For a nonempty directed inverse system of schemes with affine transition
morphisms, base change induces an equivalence from the colimit of the quasi-compact,
quasi-separated, locally finitely presented over-categories to the corresponding category over
the limit scheme. -/
@[stacks 0EY1] #check
  (AlgebraicGeometry.Scheme.Over.Qcqs.LocallyFinitePresentation.Descent.comparison_isEquivalence :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ {i j : I} (hij : i ≤ j),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE hij))],
      (AlgebraicGeometry.Scheme.Over.Qcqs.LocallyFinitePresentation.Descent.comparison
        D c hc).IsEquivalence)
