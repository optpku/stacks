module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein

/-!
# Gorenstein loci of scheme morphisms
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The subset of the source where a scheme morphism is Gorenstein at the point. -/
def gorensteinLocus (f : X ⟶ Y) : Set X :=
  {x | f.gorensteinAt x}

/-- A point lies in the Gorenstein locus exactly when the morphism is Gorenstein at that point. -/
theorem mem_gorensteinLocus (f : X ⟶ Y) (x : X) :
    x ∈ f.gorensteinLocus ↔ f.gorensteinAt x := sorry

end AlgebraicGeometry.Scheme.Hom
