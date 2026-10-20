module

public import ReasLib.AlgebraicGeometry.Scheme.Size
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Cardinal AlgebraicGeometry

universe u

/- Lemma 3.9.5: the size of a scheme is bounded by the index cardinal and the sizes
of its open covering subschemes, with the authorized countable-cardinal floor for
arbitrary, including empty, index types. -/
@[stacks 000Q] #check (AlgebraicGeometry.Scheme.size_le_isOpenCover :
  ∀ {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens), IsOpenCover U →
    X.size ≤ max ℵ₀ (max (#ι) (⨆ i, (U i).toScheme.size)))

#check (AlgebraicGeometry.Scheme.size_le_openCover :
  ∀ {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}), Nonempty 𝒰.I₀ →
    X.size ≤ max (#𝒰.I₀) (⨆ i, (𝒰.X i).size))
