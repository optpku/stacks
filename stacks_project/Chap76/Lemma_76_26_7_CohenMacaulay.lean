module

public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay

/-!
# Cohen--Macaulay locus of a morphism of algebraic spaces

The Cohen--Macaulay locus of a morphism of algebraic spaces is the set of
points at which the morphism is Cohen--Macaulay in the sense of
`CohenMacaulayAt`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The locus of points of `X` at which `f` is Cohen--Macaulay. -/
def cohenMacaulayLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points X) :=
  {x | CohenMacaulayAt f x}

/-- A point lies in the Cohen--Macaulay locus exactly when the morphism is
Cohen--Macaulay at that point. -/
theorem mem_cohenMacaulayLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ cohenMacaulayLocus f ↔ CohenMacaulayAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
