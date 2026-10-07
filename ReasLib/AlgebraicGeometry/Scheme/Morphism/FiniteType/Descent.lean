module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import ReasLib.RingTheory.RingHom.FiniteType.FaithfullyFlat

/-!
# Descent of local finite type

This file records descent of local finite type under fppf precomposition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- Local finite type descends under precomposition by a surjective, flat, locally finitely
presented morphism. -/
instance hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := sorry

/-- In a commutative triangle `f ≫ q = p`, local finite type descends from `p` to `q` when `f`
is surjective, flat, and locally of finite presentation. -/
theorem of_comp_eq_of_fppf {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType p]
    (hcomm : f ≫ q = p) : LocallyOfFiniteType q := sorry

end AlgebraicGeometry.LocallyOfFiniteType
