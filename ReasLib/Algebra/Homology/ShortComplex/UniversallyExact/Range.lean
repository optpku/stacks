module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact

@[expose] public section

open CategoryTheory LinearMap

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]

/-- If a short complex remains exact at its middle term after tensoring with every module,
then the inclusion of the range of its second map is universally injective. -/
theorem universallyInjective_rangeSubtype
    (S : ShortComplex (ModuleCat.{v} R))
    (hS : ∀ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q),
      range (rTensor Q S.f.hom) = ker (rTensor Q S.g.hom)) :
    UniversallyInjective.{u, v, v, max u v} (range S.g.hom).subtype := sorry

end CategoryTheory.ShortComplex
