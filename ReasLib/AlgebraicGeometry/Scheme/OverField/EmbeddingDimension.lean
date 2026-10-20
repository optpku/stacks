module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddingDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Embedding dimension over a field

This module relates the intrinsic embedding dimension to the dimension over a
base field at a closed point.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

noncomputable section

variable {k : Type u} [Field k]

/-- The module structure over the base field on the local cotangent space, obtained by
restricting its residue-field action along the structure morphism. -/
noncomputable abbrev cotangentSpaceModuleAt (X : SchemeOverField k) (x : X.left) :
    Module k (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) :=
  @Module.compHom (IsLocalRing.ResidueField (X.left.presheaf.stalk x)) k
    (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) _ _ _ _
    (Scheme.Hom.ResidueField.mapOfSpec X.hom x :
      k →+* IsLocalRing.ResidueField (X.left.presheaf.stalk x))

/-- The dimension over the base field of the local cotangent space at a point. -/
noncomputable def cotangentDimensionAt (X : SchemeOverField k) (x : X.left) : ℕ :=
  @Module.finrank k (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) _ _
    (cotangentSpaceModuleAt X x)

/-- At a closed point of a locally algebraic scheme over an algebraically closed field, the
intrinsic embedding dimension equals the base-field dimension of the local cotangent space. -/
theorem embeddingDimensionAt_eq_cotangentDimensionAt_of_closedPoint
    [IsAlgClosed k] (X : SchemeOverField k) [LocallyAlgebraic X]
    (x : X.left) (hx : IsClosed {x}) :
    Scheme.embeddingDimensionAt x = cotangentDimensionAt X x := sorry

end

end AlgebraicGeometry.SchemeOverField
