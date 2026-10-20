module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

/-!
# Points of an algebraic stack

A point of an algebraic stack `X` over a scheme `S` is an equivalence class of morphisms
`Spec(K) ⟶ X` from spectra of fields. Two such morphisms are equivalent when they become
2-isomorphic after restriction along a common field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The set of points of an algebraic stack, as equivalence classes of morphisms from spectra of
fields. -/
def Points {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Type (u + 1) :=
  Quotient (equivalentSetoid X)

/-- The set of points of an algebraic stack `X`. -/
scoped notation:max "|" X:max "|" => Points X

namespace Points

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The class of a field-valued point. -/
def mk (p : FieldValuedPoint X) : Points X :=
  Quotient.mk (equivalentSetoid X) p

/-- Two field-valued points determine the same point of `X` exactly when they admit a common
field-valued extension. -/
@[simp]
theorem mk_eq_mk_iff (p q : FieldValuedPoint X) :
    mk p = mk q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The map on points induced by a morphism of algebraic stacks over `S`. -/
def map {Y : GroupoidsOver S} [AlgebraicStack Y] (f : X ⟶ Y) : Points X → Points Y :=
  Quotient.map (fun p ↦ p.map f) fun _ _ h ↦ FieldValuedPoint.Equivalent.map h f

/-- The induced map on points sends the class of a representative to the class of its
postcomposition. -/
@[simp]
theorem map_mk {Y : GroupoidsOver S} [AlgebraicStack Y] (f : X ⟶ Y) (p : FieldValuedPoint X) :
    map f (mk p) = mk (p.map f) := sorry

/-- The identity morphism of algebraic stacks induces the identity on points. -/
@[simp]
theorem map_id (x : Points X) : map (𝟙 X) x = x := sorry

/-- The induced map on points preserves composition. -/
@[simp]
theorem map_comp {Y Z : GroupoidsOver S} [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) : map (f ≫ g) x = map g (map f x) := sorry

end Points

end AlgebraicGeometry.AlgebraicStack
