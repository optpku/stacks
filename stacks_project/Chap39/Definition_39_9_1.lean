module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety

universe u

/- The source-facing owner for this item is `AlgebraicGeometry.AbelianVariety`, a class on
group schemes over a field. Its companion theorem
`AlgebraicGeometry.abelianVariety_iff` recovers exactly the source conditions:
the underlying scheme is a proper variety and the structure morphism is geometrically
integral. -/

/- Definition 39.9.1: an abelian variety over a field `k` is a group scheme over `k`
whose underlying scheme is a proper variety and whose structure morphism is geometrically
integral; this is the canonical class `AlgebraicGeometry.AbelianVariety`. -/
@[stacks 03RO] #check (AlgebraicGeometry.AbelianVariety :
  ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
    [CategoryTheory.GrpObj G], Prop)

#check (AlgebraicGeometry.abelianVariety_iff :
  ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
    [CategoryTheory.GrpObj G],
    AlgebraicGeometry.AbelianVariety G ↔
      AlgebraicGeometry.ProperVariety G ∧
        AlgebraicGeometry.GeometricallyIntegral G.hom)
