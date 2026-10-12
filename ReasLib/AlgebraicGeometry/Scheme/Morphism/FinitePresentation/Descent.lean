/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import ReasLib.RingTheory.RingHom.FinitePresentation.FaithfullyFlat

/-!
# Descent of local finite presentation

This file records descent of local finite presentation under fppf precomposition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-- Local finite presentation descends under precomposition by a surjective, flat, locally
finitely presented morphism. -/
instance hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := sorry

/-- In a commutative triangle `f ≫ q = p`, local finite presentation descends from `p` to `q`
when `f` is surjective, flat, and locally of finite presentation. -/
theorem of_comp_eq_of_fppf {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation p] (hcomm : f ≫ q = p) :
    LocallyOfFinitePresentation q := sorry

end AlgebraicGeometry.LocallyOfFinitePresentation
