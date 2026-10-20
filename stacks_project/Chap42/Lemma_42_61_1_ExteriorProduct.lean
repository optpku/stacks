module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import stacks_project.Chap42.Remark_42_33_5_Bivariant

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- The reusable cycle exterior-product pairing has the source-facing degree convention. -/
#check (AlgebraicGeometry.CycleGroup.exteriorProductPairing :
  {k : Type u} → [Field k] →
    (X Y : AlgebraicGeometry.SchemeOverField k) →
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] →
    (n m : ℤ) →
    AlgebraicGeometry.CycleGroup X.left
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n →+
      AlgebraicGeometry.CycleGroup Y.left
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m →+
        AlgebraicGeometry.CycleGroup (X ⨯ Y).left
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) (n + m))

/- The reusable Chow exterior-product pairing agrees with the source-facing relative Chow
notation and degree convention. -/
#check (AlgebraicGeometry.ChowGroup.exteriorProductPairing :
  {k : Type u} → [Field k] →
    (X Y : AlgebraicGeometry.SchemeOverField k) →
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] →
    (n m : ℤ) →
    AlgebraicGeometry.RelativeChow (fun _ ↦ 0) X n →+
      AlgebraicGeometry.RelativeChow (fun _ ↦ 0) Y m →+
        AlgebraicGeometry.RelativeChow (fun _ ↦ 0) (X ⨯ Y) (n + m))
