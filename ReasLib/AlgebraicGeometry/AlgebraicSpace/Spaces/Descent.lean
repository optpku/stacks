/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Prestack
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Algebraic spaces satisfy effective descent for objects along an fppf covering
family whose index type is small in the scheme universe. Every descent datum is
isomorphic to the canonical descent datum of an algebraic space over the base. -/
theorem essSurj_ofArrows {S : Scheme.{u}} {U : Over S}
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U) :
    ((Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).toDescentData f).EssSurj :=
  sorry

/-- The fiber pseudofunctor of algebraic spaces satisfies the stack condition
along every fppf covering family whose index type is small in the scheme universe. -/
theorem isStackFor_ofArrows {S : Scheme.{u}} {U : Over S}
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U) :
    (Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).IsStackFor
      (Presieve.ofArrows Ui f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
