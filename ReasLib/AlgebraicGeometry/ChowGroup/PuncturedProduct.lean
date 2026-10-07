module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.ChowGroup.Localization
public import ReasLib.AlgebraicGeometry.ChowGroup.RationalPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PuncturedOpen
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- For smooth projective geometrically irreducible curves over a field with rational points
and points of residue degree two, the product rational-point class restricts to a nonzero
degree-zero Chow class on the product of the complements of the degree-two points. -/
@[stacks 05WK]
theorem puncturedProduct_rationalPointClass_ne_zero
    {k : Type u} [Field k] {n : ℕ} (C : Fin n → SchemeOverField k)
    [∀ i, Curve (C i)] [∀ i, Smooth (C i).hom] [∀ i, Projective (C i).hom]
    [∀ i, GeometricallyIrreducible (C i).hom]
    (P : (i : Fin n) → 𝟙_ (SchemeOverField k) ⟶ C i)
    (Q : (i : Fin n) → (C i).left)
    (hQ : ∀ i, (C i).hom.residueDegree (Q i) = 2) :
    Localization.openPullback (∏ᶜ C).hom (fun _ ↦ (0 : ℤ))
      (SchemeOverField.puncturedProductOpen C Q) 0
      (rationalPointClass (∏ᶜ C) (Pi.lift P)) ≠ 0 := sorry

end AlgebraicGeometry.ChowGroup
