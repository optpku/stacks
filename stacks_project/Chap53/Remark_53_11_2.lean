module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Genus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product.Properties

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.Limits

universe u

/- Remark 53.11.2 (1): for a proper variety `X` over a field, its arithmetic genus is
`(-1) ^ X.dimension * (χ(X, 𝒪_X) - 1)`. -/
@[stacks 0BYG] #check
  (AlgebraicGeometry.SchemeOverField.arithmeticGenus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X] [IsProper X.hom], ℤ)

/- Remark 53.11.2 (2): for a smooth proper variety `X`, its geometric genus is
`dim_k H⁰(X, Λ[X.dimension] Ω[X.hom.toShHom])`. -/
@[stacks 0BYG] #check
  (AlgebraicGeometry.SchemeOverField.geometricGenus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X] [IsProper X.hom]
      [SmoothOfRelativeDimension X.dimension X.hom], ℕ)

/- Remark 53.11.2 (3): the dualizing module of a smooth proper `d`-dimensional variety is
isomorphic to `Λ[d] Ω[f.toShHom]`. -/
@[stacks 0BYG] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.smooth_dualizingModule_isomorphic_exteriorPower :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (d : ℕ)
      [SmoothOfRelativeDimension d f],
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f)
        (RingedSpace.ExteriorPower.sheaf (Ω[f.toShHom]) d))

/- Remark 53.11.2 (4): on a smooth proper surface over an algebraically closed field, the
difference between geometric and arithmetic genus is its irregularity. -/
@[stacks 0BYG] #check
  (AlgebraicGeometry.SchemeOverField.surfaceGenusDifference_eq_irregularity :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Variety X] [IsProper X.hom]
      [SmoothOfRelativeDimension X.dimension X.hom]
      (h_dimension : X.dimension = 2),
      (AlgebraicGeometry.SchemeOverField.geometricGenus X : ℤ) -
          AlgebraicGeometry.SchemeOverField.arithmeticGenus X =
        (AlgebraicGeometry.SchemeOverField.irregularity X : ℤ))

/- Remark 53.11.2 (5): the geometric genus of a smooth proper surface over an algebraically
closed field is at least its arithmetic genus. -/
@[stacks 0BYG] #check
  (AlgebraicGeometry.SchemeOverField.surfaceGenusDifference_nonnegative :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Variety X] [IsProper X.hom]
      [SmoothOfRelativeDimension X.dimension X.hom]
      (h_dimension : X.dimension = 2),
      0 ≤
        (AlgebraicGeometry.SchemeOverField.geometricGenus X : ℤ) -
          AlgebraicGeometry.SchemeOverField.arithmeticGenus X)

/- Remark 53.11.2 (6): the irregularity of a product of two smooth projective geometrically
irreducible curves is the sum of their genera. -/
@[stacks 0BYG] #check
  (AlgebraicGeometry.SchemeOverField.irregularity_prod_curves :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (C₁ C₂ : SchemeOverField k)
      [Curve C₁] [Projective C₁.hom] [Smooth C₁.hom]
      [GeometricallyIrreducible C₁.hom]
      [Curve C₂] [Projective C₂.hom] [Smooth C₂.hom]
      [GeometricallyIrreducible C₂.hom],
      AlgebraicGeometry.SchemeOverField.irregularity (C₁ ⨯ C₂) =
        Curve.genus C₁ + Curve.genus C₂)
