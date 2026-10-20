/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.DenseOpen
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.51.5: a locally finite type morphism whose source and target have finitely many
generic points, and whose inverse image of the target generic points is exactly the source generic
points, is finite over a dense open of the target when it is quasi-compact or separated. -/
@[stacks 0BAI] #check
  (AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_restrict_of_preimage_genericPoints_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f],
      (genericPoints X).Finite →
      (genericPoints Y).Finite →
      f.base ⁻¹' genericPoints Y = genericPoints X →
      QuasiCompact f ∨ IsSeparated f →
      ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V))
