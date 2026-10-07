module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Definition 29.15.1: finite type at a point is the affine-neighborhood condition, locally
finite type means finite type at every source point, and finite type means locally finite type
and quasi-compact. -/
@[stacks 01T1] #check
  (AlgebraicGeometry.Scheme.Hom.finiteType_iff_quasiCompact_and_forall_finiteTypeAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Hom.FiniteType f ↔
        AlgebraicGeometry.QuasiCompact f ∧
          ∀ x : X, AlgebraicGeometry.Scheme.Hom.FiniteTypeAt f x)

#check
  (AlgebraicGeometry.Scheme.Hom.finiteTypeAt_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      AlgebraicGeometry.Scheme.Hom.FiniteTypeAt f x ↔
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ V : S.affineOpens,
            ∃ e : U ≤ f ⁻¹ᵁ V,
              (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType)

#check
  (AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_iff_forall_finiteTypeAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyOfFiniteType f ↔
        ∀ x : X, AlgebraicGeometry.Scheme.Hom.FiniteTypeAt f x)
