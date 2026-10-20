module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Factorizations of field-valued points

A factorization of field-valued points induces a morphism between the corresponding slice objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization

/-- The morphism of slices `Over.mk p.hom ⟶ Over.mk q.hom` induced by a factorization of
field-valued points. -/
def sliceHom {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : Factorization p q) : Over.mk p.hom ⟶ Over.mk q.hom :=
  Over.homMk (ofOverHomMk φ.schemeHom φ.fac_structure) φ.fac_hom

/-- The underlying morphism of algebraic spaces of `sliceHom φ` is `ofOverHomMk` of the scheme
map. -/
theorem sliceHom_left {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : Factorization p q) :
    (sliceHom φ).left = ofOverHomMk φ.schemeHom φ.fac_structure :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization
