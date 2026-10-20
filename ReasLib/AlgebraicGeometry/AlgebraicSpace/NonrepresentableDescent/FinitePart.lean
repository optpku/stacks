module

public import ReasLib.FieldTheory.Complex
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf

/-! # A finite origin morphism with a nonrepresentable finite-part sheaf -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- The morphism from `Spec(ℂ)` to the real affine line at its rational origin is finite. -/
instance instIsFinite_originOver_realComplex :
    AlgebraicGeometry.IsFinite (originOver ℝ ℂ).hom := sorry

/-- The origin morphism `Spec(ℂ) ⟶ A¹_ℝ` as a morphism of algebraic spaces over `A¹_ℝ`. -/
def originMorphism : ofOver (originOver ℝ ℂ) ⟶ ofOver (baseAsOver ℝ) :=
  ofOverMap (toBaseAsOver ℝ (originOver ℝ ℂ))

/-- The finite-part fppf sheaf of the origin morphism `Spec(ℂ) ⟶ A¹_ℝ`. -/
def originFinitePart : Sheaf (Scheme.fppfTopology.over (base ℝ)) (Type 1) :=
  finitePartSheaf originMorphism

/-- The finite-part sheaf of the complex origin over the real affine line is isomorphic
 to the quadratic Galois quotient sheaf associated to `ℝ ⊂ ℂ`. -/
theorem originFinitePart_iso_sheafOfPoints :
    Nonempty (originFinitePart ≅ sheafOfPoints ℝ ℂ Complex.finrank_real_complex) :=
  sorry

/-- The finite-part sheaf of the complex origin over the real affine line is not
representable by a scheme over the real affine line. -/
theorem not_isRepresentable_originFinitePart :
    ¬ ∃ T : Over (base ℝ),
        Nonempty
          (originFinitePart ≅
            (Scheme.fppfTopology.over (base ℝ)).uliftYoneda.{1}.obj T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
