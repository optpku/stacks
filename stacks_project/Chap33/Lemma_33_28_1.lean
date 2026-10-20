/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.Basic

/-!
# Lemma 33.28.1

For a normal open subscheme of a proper variety over an algebraically closed
field, global units modulo scalar units are finitely generated.  This is the
canonical `SchemeOverField.GlobalUnits.moduleFinite_of_normalOpen` API.
-/

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.28.1: If `U` is a normal open subscheme of a proper variety over an algebraically
closed field, then its global units modulo scalar units form a finitely generated abelian group. -/
@[stacks 04L4] #check
  (AlgebraicGeometry.SchemeOverField.GlobalUnits.moduleFinite_of_normalOpen :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsAlgClosed k]
      [AlgebraicGeometry.Variety X] [AlgebraicGeometry.IsProper X.hom]
      (U : X.left.Opens), U.toScheme.isNormal →
        Module.Finite ℤ
          (Additive (AlgebraicGeometry.Scheme.Hom.unitsQuotient (U.ι ≫ X.hom))))
