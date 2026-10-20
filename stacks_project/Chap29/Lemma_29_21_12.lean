/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Diagonal
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.21.12 (1): if `f : X ⟶ Y` is locally of finite type, then its diagonal
`pullback.diagonal f : X ⟶ X ×[Y] X` is locally of finite presentation. -/
@[stacks 0818] #check
  (AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f],
      LocallyOfFinitePresentation (pullback.diagonal f))

/- Lemma 29.21.12 (2): if `f : X ⟶ Y` is quasi-separated and locally of finite type, then its
diagonal `pullback.diagonal f : X ⟶ X ×[Y] X` is of finite presentation. -/
@[stacks 0818] #check
  (AlgebraicGeometry.Scheme.Hom.finitePresentation_diagonal_of_quasiSeparated_of_locallyOfFiniteType :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f],
      Scheme.Hom.FinitePresentation (pullback.diagonal f))
