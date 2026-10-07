module

public import stacks_project.Chap03.Lemma_3_9_5_Size

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Cardinal AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.5: if `U` is a nonempty-indexed open covering of a scheme `X`, then the size of `X`
is at most the maximum of the cardinality of the index type and the supremum of the sizes of the
open subschemes `(U i).toScheme`. -/
@[stacks 000Q]
theorem size_le_isOpenCover {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hι : Nonempty ι) :
    X.size ≤ max (#ι) (⨆ i, (U i).toScheme.size) := sorry

/-- The size of a scheme is at most the maximum of the index cardinal of a nonempty-indexed open
cover and the supremum of the sizes of the covering schemes. -/
theorem size_le_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) (hI : Nonempty 𝒰.I₀) :
    X.size ≤ max (#𝒰.I₀) (⨆ i, (𝒰.X i).size) := sorry

end AlgebraicGeometry.Scheme
