/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected colimits of commutative algebras

This leaf records the categorical fact that the underlying commutative-ring
cocone of a connected colimit of commutative algebras is still colimiting.
The connectedness hypothesis is exact: arbitrary coproducts of algebras need
not be coproducts of their underlying rings.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CommAlgCat.ConnectedColimit

variable {R : Type u} [CommRing R]
variable {I : Type v} [Category I] [IsConnected I]

/-- Forgetting a connected colimit cocone of commutative `R`-algebras to
`CommRingCat` preserves its colimit property. -/
@[stacks 00QV "connected commutative-algebra colimit"]
noncomputable def forgetCommRingIsColimit
    (F : I ⥤ CommAlgCat.{u} R) (c : ColimitCocone F) :
    IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat).mapCocone c.cocone) :=
  isColimitOfPreserves (Under.forget (CommRingCat.of R))
    (isColimitOfPreserves (commAlgCatEquivUnder (CommRingCat.of R)).functor c.isColimit)

end CommAlgCat.ConnectedColimit
