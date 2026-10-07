module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Hilbert.UniversalDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints

/-!
# Abel maps of smooth projective curves

This file constructs the Abel map from the Hilbert scheme of effective divisors to a
degree component of the relative Picard scheme and records its geometric properties.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.RelativePicard

/-- A smooth curve over a field is smooth of relative dimension one over that field. -/
instance curveSmoothOfRelativeDimensionOne
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [Smooth X.hom] :
    SmoothOfRelativeDimension 1 X.hom := sorry

/-- The universal Hilbert divisor is an effective Cartier divisor in every nonnegative
degree. -/
instance universalDivisor_isEffectiveCartier
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    IsEffectiveCartierDivisor (Hilbert.universalDivisor X d).subschemeι := sorry

/-- The universal Hilbert divisor of any nonnegative degree has an invertible associated
module. -/
instance universalDivisorAssociatedSheaf_isInvertible
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    Scheme.Modules.Invertible (Hilbert.universalDivisor X d).associatedSheaf := sorry

/-- Pulling the universal divisor's associated module across the factor-exchange
isomorphism preserves its invertibility. -/
instance pullbackUniversalDivisorAssociatedSheaf_isInvertible
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    Scheme.Modules.Invertible
      ((Scheme.Modules.pullback
        (β_ (Hilbert.functor X d).reprX X).hom.left).obj
          (Hilbert.universalDivisor X d).associatedSheaf) := sorry

/-- The Picard class of the universal degree-`d` divisor, transported from
`X ×ₖ Hilb^d_{X/k}` to `Hilb^d_{X/k} ×ₖ X`. -/
noncomputable def abelPicardClass
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    (presheaf X).obj (op (Hilbert.functor X d).reprX) :=
  Scheme.Modules.picardClass
    ((Scheme.Modules.pullback
      (β_ (Hilbert.functor X d).reprX X).hom.left).obj
        (Hilbert.universalDivisor X d).associatedSheaf)

/-- The universal degree-`d` Picard class is the class of the universal divisor's
associated invertible module after exchanging the factors of the fibre product. -/
theorem abelPicardClass_eq_picardClass
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    abelPicardClass X d =
      Scheme.Modules.picardClass
        ((Scheme.Modules.pullback
          (β_ (Hilbert.functor X d).reprX X).hom.left).obj
            (Hilbert.universalDivisor X d).associatedSheaf) := sorry

/-- The image of the universal divisor class in the fppf-sheafified Picard functor. -/
noncomputable def abelSection
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    (functor X).obj.obj (op (Hilbert.functor X d).reprX) :=
  (eqToHom (functor_val X).symm).app _
    (((Scheme.fppfTopology.over (Spec (CommRingCat.of k))).toSheafify
      (presheaf X)).app _ (abelPicardClass X d))

/-- The universal divisor class has relative degree `d`. -/
theorem abelSection_mem_degreeSubfunctor
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    abelSection X d ∈ (degreeSubfunctor X (d : ℤ)).obj
      (op (Hilbert.functor X d).reprX) := sorry

/-- The universal divisor class regarded as a section of the degree-`d` Picard subfunctor. -/
noncomputable def abelComponentSection
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    (degreeSubfunctor X (d : ℤ)).obj (op (Hilbert.functor X d).reprX) :=
  ⟨abelSection X d, abelSection_mem_degreeSubfunctor X d⟩

/-- For every nonnegative `d`, the universal effective divisor defines the canonical Abel
morphism from `Hilb^d_{X/k}` to `Pic^d_{X/k}`. -/
noncomputable def abelMap
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℕ) :
    (Hilbert.functor X d).reprX ⟶ component X (d : ℤ) :=
  (componentRepresentation X (d : ℤ)).homEquiv.symm (abelComponentSection X d)

/-- The Abel morphism is represented by the Picard-functor section of the universal divisor. -/
theorem abelMap_homEquiv
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] (d : ℕ) :
    (componentRepresentation X (d : ℤ)).homEquiv (abelMap X d) =
      abelComponentSection X d := sorry

/-- The Abel morphism is surjective when its degree is at least the genus. -/
instance abelMap_surjective
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom]
    (d : ℕ) [Fact (Curve.genus X ≤ d)] : Surjective (abelMap X d).left := sorry

/-- The Abel morphism is smooth in degree at least `2 * Curve.genus X - 1`. -/
instance abelMap_smooth
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom]
    (d : ℕ) [Fact (2 * Curve.genus X - 1 ≤ d)] : Smooth (abelMap X d).left := sorry

/-- The Abel morphism in degree equal to the genus is birational. -/
instance abelMap_genus_isBirational
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] :
    IsBirational (abelMap X (Curve.genus X)).left := sorry

end AlgebraicGeometry.RelativePicard
