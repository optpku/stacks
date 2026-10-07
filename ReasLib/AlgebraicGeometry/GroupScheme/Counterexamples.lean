module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.GroupScheme

/-- For every field, there is a flat group scheme of finite type over the affine line
whose structure morphism is not separated. -/
theorem exists_flat_finiteType_not_isSeparated_over_affineLine
    {k : Type u} [Field k] :
    ∃ G : GroupScheme (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of k))),
      AlgebraicGeometry.Flat G.X.hom ∧ Scheme.Hom.FiniteType G.X.hom ∧
        ¬ AlgebraicGeometry.IsSeparated G.X.hom := sorry

end AlgebraicGeometry.GroupScheme
