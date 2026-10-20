module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Restriction of field-valued points along field extensions

A field extension induces a morphism of spectra over the base scheme and a
field-valued point obtained by precomposition. The induced point factors
through the original point and remains locally of finite type for a finite
extension of a field locally of finite type over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The morphism `Spec(l) ⟶ Spec(k)` induced by a field extension `k → l`. -/
def restrictSchemeHom (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] : Spec (.of l) ⟶ Spec (.of x0.K) :=
  Spec.map (CommRingCat.ofHom (algebraMap x0.K l))

/-- `restrictSchemeHom` is `Spec` of the structure map `k → l`. -/
theorem restrictSchemeHom_eq (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    restrictSchemeHom x0 l = Spec.map (CommRingCat.ofHom (algebraMap x0.K l)) :=
  sorry

/-- The morphism `Over.mk (Spec(l) ⟶ S) ⟶ Over.mk (Spec(k) ⟶ S)` with left
component `restrictSchemeHom`. -/
def restrictOverHom (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    Over.mk (restrictSchemeHom x0 l ≫ x0.structureHom) ⟶ Over.mk x0.structureHom :=
  Over.homMk (restrictSchemeHom x0 l) rfl

/-- `restrictOverHom` has left component `restrictSchemeHom`. -/
theorem restrictOverHom_left (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    (restrictOverHom x0 l).left = restrictSchemeHom x0 l := sorry

/-- The field-valued point `x_{l,0}` induced by a field extension `l / k` of
the source of `x0`. -/
def restrict (x0 : FieldValuedPoint X) (l : Type u) [Field l] [Algebra x0.K l] :
    FieldValuedPoint X :=
  FieldValuedPoint.of l (restrictSchemeHom x0 l ≫ x0.structureHom)
    (overMap (restrictOverHom x0 l) ≫ x0.hom)

/-- The induced point `x0.restrict l` has source field `l`, structure morphism
`Spec(l) ⟶ Spec(k) ⟶ S`, and 1-morphism obtained by precomposing `x0.hom`
with `overMap`. -/
theorem restrict_spec (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    (x0.restrict l).K = l ∧
      (x0.restrict l).structureHom = restrictSchemeHom x0 l ≫ x0.structureHom ∧
        (x0.restrict l).hom = overMap (restrictOverHom x0 l) ≫ x0.hom :=
  sorry

/-- The induced morphism `x_{l,0} → x0` as a factorization of field-valued
points over `S`. -/
def restrictFactorization (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] : Factorization (x0.restrict l) x0 :=
  Factorization.of (restrictSchemeHom x0 l) rfl (Iso.refl _)

/-- `restrictFactorization` is `Spec` of `k → l` and the triangle over `S`
commutes. -/
theorem restrictFactorization_spec (x0 : FieldValuedPoint X) (l : Type u)
    [Field l] [Algebra x0.K l] :
    (x0.restrictFactorization l).schemeHom = restrictSchemeHom x0 l ∧
      (x0.restrictFactorization l).schemeHom ≫ x0.structureHom =
        (x0.restrict l).structureHom :=
  sorry

/-- Finite extensions of a finite-type field over `S` remain locally of finite
type over `S`. -/
instance instLocallyOfFiniteType_restrict (x0 : FieldValuedPoint X)
    (l : Type u) [Field l] [Algebra x0.K l]
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    [Module.Finite x0.K l] :
    AlgebraicGeometry.LocallyOfFiniteType (x0.restrict l).structureHom :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

