module

public import Mathlib.Order.Lattice.Nat
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.SmoothModels

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.NonsingularProjectiveModel.WithIso

/-- The genus of a nonsingular projective model, computed as the dimension of the first
cohomology of its structure sheaf. -/
noncomputable def genus {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (Y : WithIso X) : ℕ :=
  Scheme.Hom.cohomologyFinrank Y.curve.hom
    (SheafOfModules.unit Y.curve.left.ringCatSheaf : Y.curve.left.Modules) 1

/-- The model genus is the degree-one cohomology dimension of its structure sheaf. -/
theorem genus_def {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (Y : WithIso X) :
    Y.genus = Scheme.Hom.cohomologyFinrank Y.curve.hom
      (SheafOfModules.unit Y.curve.left.ringCatSheaf : Y.curve.left.Modules) 1 := sorry

/-- On a smooth geometrically irreducible model, the model genus agrees with the ordinary
genus of its underlying curve. -/
theorem genus_eq_curveGenus {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (Y : WithIso X) [Smooth Y.curve.hom] [GeometricallyIrreducible Y.curve.hom] :
    Y.genus = @Curve.genus k _ Y.curve Y.isCurve Y.projective _ _ := sorry

end AlgebraicGeometry.NonsingularProjectiveModel.WithIso

namespace AlgebraicGeometry.Curve

/-- The geometric genus of a geometrically irreducible curve is the common genus of its
smooth projective models over field extensions. -/
noncomputable def geometricGenus {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] : ℕ :=
  sInf {n : ℕ | ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
    (h_curve : Curve (FieldExtension.Reduced.baseChange k K X))
    (Y : @NonsingularProjectiveModel.WithIso K _
      (FieldExtension.Reduced.baseChange k K X) h_curve),
    Smooth Y.curve.hom ∧ n = Y.genus}

/-- The geometric genus equals the genus of every smooth projective model over any extension
of the ground field. -/
theorem geometricGenus_eq_modelGenus
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    (Y : NonsingularProjectiveModel.WithIso
      (FieldExtension.Reduced.baseChange k K X)) [Smooth Y.curve.hom] :
    geometricGenus X = Y.genus := sorry

/-- The geometric genus is realized by a smooth model after a finite purely inseparable
extension of the ground field. -/
theorem exists_geometricGenusModel
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : FiniteDimensional k K) (_ : IsPurelyInseparable k K)
      (Y : NonsingularProjectiveModel.WithIso
        (FieldExtension.Reduced.baseChange k K X)),
      Smooth Y.curve.hom ∧ geometricGenus X = Y.genus := sorry

/-- For a smooth projective curve, geometric genus agrees with the ordinary curve genus. -/
theorem geometricGenus_eq_genus
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [Smooth X.hom] [Projective X.hom] :
    geometricGenus X = genus X := sorry

end AlgebraicGeometry.Curve
