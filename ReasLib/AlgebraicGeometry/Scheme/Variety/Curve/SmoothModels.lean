module

public import Mathlib.FieldTheory.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Reduced.Curve
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Normalization.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Model

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.NonsingularProjectiveModel.WithIso

/-- Over a perfect field, every nonsingular projective model of a curve is smooth. -/
theorem smooth_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : SchemeOverField k} [Curve X] (Y : WithIso X) : Smooth Y.curve.hom := sorry

/-- Every nonsingular projective model of the reduced base change of a geometrically
irreducible proper curve is isomorphic over the extension field to the normalization of
the base change. -/
theorem isIsomorphic_normalizationBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (Y : WithIso (FieldExtension.Reduced.baseChange k K X)) :
    IsIsomorphic Y.curve (FieldExtension.Normalization.baseChange X K) := sorry

/-- A geometrically irreducible curve has a smooth nonsingular projective model of its
reduced base change after a finite purely inseparable extension of the ground field. -/
theorem exists_smooth
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [GeometricallyIrreducible X.hom] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : FiniteDimensional k K) (_ : IsPurelyInseparable k K)
      (Y : WithIso (FieldExtension.Reduced.baseChange k K X)),
      Smooth Y.curve.hom := sorry

/-- For a smooth nonsingular projective model of the reduced base change of a geometrically
irreducible curve, the canonical map from the extension field to global sections is bijective. -/
theorem globalSectionsMap_bijective_of_smooth
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    (Y : WithIso (FieldExtension.Reduced.baseChange k K X))
    [Smooth Y.curve.hom] :
    Function.Bijective (Scheme.Hom.globalSectionsMap Y.curve.hom) := sorry

/-- Smooth nonsingular projective models over two extensions of the ground field become
isomorphic over a common extension to any nonsingular projective model of the reduced base
change to that common extension. -/
theorem baseChange_isIsomorphic
    {k K K' Ω : Type u} [Field k] [Field K] [Field K'] [Field Ω]
    [Algebra k K] [Algebra k K'] [Algebra k Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower k K Ω] [IsScalarTower k K' Ω]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    (Y_K : WithIso (FieldExtension.Reduced.baseChange k K X))
    (Y_K' : WithIso (FieldExtension.Reduced.baseChange k K' X))
    (Y_Ω : WithIso (FieldExtension.Reduced.baseChange k Ω X))
    [Smooth Y_K.curve.hom] [Smooth Y_K'.curve.hom] :
    IsIsomorphic Y_Ω.curve (FieldExtension.Over.baseChange K Ω Y_K.curve) ∧
      IsIsomorphic Y_Ω.curve (FieldExtension.Over.baseChange K' Ω Y_K'.curve) := sorry

end AlgebraicGeometry.NonsingularProjectiveModel.WithIso
