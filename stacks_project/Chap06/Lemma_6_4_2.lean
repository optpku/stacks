module

public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

variable {X : TopCat.{u}} (U : Opens X) (ℱ 𝒢 : X.Presheaf (Type v))

/- Lemma 6.4.2 (1): set-valued presheaves on `X` have products. The canonical presheaf
`HasLimitsOfShape` instance supplied by `Mathlib.Topology.Sheaves.Limits` is the exact owner; the
source's binary product is its specialization to a two-object discrete diagram. -/
@[stacks 006I "set-valued presheaves have products"]
#check (inferInstance : HasProducts (X.Presheaf (Type v)))

/- Lemma 6.4.2 (2): over an open `U`, sections of the categorical product presheaf are canonically
equivalent to pairs of sections. `FunctorToTypes.binaryProductEquiv` is already stated at the
general functor-category layer, and specialization to `(Opens X)ᵒᵖ` recovers the source exactly. -/
@[stacks 006I "sections of a product presheaf are pairs of sections"]
#check (FunctorToTypes.binaryProductEquiv ℱ 𝒢 (op U))
