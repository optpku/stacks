/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A]

/- Lemma 13.10.5 (1): bounded-below homotopy objects form a full triangulated subcategory of
`HomotopyCategory A (ComplexShape.up ℤ)`. -/
@[stacks 05RQ "bounded-below homotopy subcategory"] #check
  (inferInstance : (HomotopyCategory.plus A).IsTriangulated)

/- Lemma 13.10.5 (2): bounded-above homotopy objects form a full triangulated subcategory of
`HomotopyCategory A (ComplexShape.up ℤ)`. -/
@[stacks 05RQ "bounded-above homotopy subcategory"] #check
  (inferInstance : (HomotopyCategory.minus A).IsTriangulated)

/- Lemma 13.10.5 (3): bounded homotopy objects form a full triangulated subcategory of
`HomotopyCategory A (ComplexShape.up ℤ)`. -/
@[stacks 05RQ "bounded homotopy subcategory"] #check
  (inferInstance : (HomotopyCategory.bounded A).IsTriangulated)

/- The induced full subcategories inherit their triangulated category structures. -/
#check (inferInstance : IsTriangulated (K⁺(A)))
#check (inferInstance : IsTriangulated (K⁻(A)))
#check (inferInstance : IsTriangulated (Kᵇ(A)))

end CategoryTheory
