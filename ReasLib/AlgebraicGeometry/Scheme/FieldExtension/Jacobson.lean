module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson
public import ReasLib.RingTheory.Jacobson.Cardinality

/-!
# Jacobson schemes after large field extensions

This file records cardinality bounds that ensure algebraicity of residue fields at closed points
and the Jacobson property after extending the base field of a scheme.
-/

@[expose] public section

open Cardinal
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FieldExtension

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- After extending the base field beyond a cardinal bound, every closed point of the base change
has residue field algebraic over the extended base field. -/
theorem exists_cardinal_residueField_isAlgebraic_of_closedPoint :
    ∃ κ : Cardinal.{u}, ∀ {K : Type u} [Field K] [Algebra k K],
      κ < #K →
        ∀ x : FieldExtension.baseChange k K f,
          x ∈ closedPoints (FieldExtension.baseChange k K f) →
            Scheme.Hom.ResidueField.IsAlgebraicOverSpec (FieldExtension.toBase k K f) x := sorry

/-- After extending the base field beyond a cardinal bound, the base change of a scheme is a
Jacobson space. -/
theorem exists_cardinal_jacobsonSpace :
    ∃ κ : Cardinal.{u}, ∀ {K : Type u} [Field K] [Algebra k K],
      κ < #K → JacobsonSpace (FieldExtension.baseChange k K f) := sorry

end AlgebraicGeometry.FieldExtension
