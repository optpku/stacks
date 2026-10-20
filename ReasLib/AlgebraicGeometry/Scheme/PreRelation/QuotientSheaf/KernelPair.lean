module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The two projections of an internal equivalence relation form the kernel pair of its
canonical quotient map in the category of fppf sheaves. -/
theorem isKernelPair_quotientMap {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] :
    IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s) := sorry

end AlgebraicGeometry.Scheme.PreRelation
