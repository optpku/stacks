import AnnalsChallenge.AnnalsOfMathematics.«2021-194-1-UniformMordellLang»

/- Interface and mathematical-specification checks. These assert the original
field/curve hypotheses and quantifier order. They do not prove the deferred
geometric or Diophantine theorems. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.JacobianChallenge
open CommGroup Module

universe u

-- Compare unapplied, fully explicit constants with the original function types.
-- Unlike call-site tests, these cannot silently synthesize an extra hypothesis.
example : ∀ {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom], ℕ := @genus

example : ∀ {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom], Over (Spec (.of k)) := @Jacobian

example : ∀ {k : Type u} [Field k] {C : Over (Spec (.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom], GrpObj (Jacobian C) := @Jacobian.instGrpObj

example : ∀ {k : Type u} [Field k] {C : Over (Spec (.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom],
    (𝟙_ (Over (Spec (.of k))) ⟶ C) → (C ⟶ Jacobian C) := @Jacobian.ofCurve

example : ℕ → ℕ → ℕ := UniformMordellLang.c

section Curves

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom]

local instance : Curve C := CurveJacobian.PicardConstruction.targetCurve C

local instance : (RelativePicard.degreeSubfunctor C 0).toFunctor.IsRepresentable :=
  CurveJacobian.PicardConstruction.degreeZeroRepresentable C

-- No algebraic-closure, characteristic-zero, projectivity, or rational-point
-- hypothesis has been added to the challenge's Jacobian construction.
example : Over (Spec (.of k)) := Jacobian C
example : GrpObj (Jacobian C) := inferInstance
example : SmoothOfRelativeDimension (genus C) (Jacobian C).hom := inferInstance
example : IsProper (Jacobian C).hom := inferInstance
example : GeometricallyIrreducible (Jacobian C).hom := inferInstance
example : GeometricallyIntegral (Jacobian C).hom := inferInstance
example : CommGroup (𝟙_ (Over (Spec (.of k))) ⟶ Jacobian C) := inferInstance

-- The public challenge definitions reduce to the independent library's actual
-- derived-cohomology and degree-zero Picard constructions.
example : genus C = CurveJacobian.genus C := rfl
example : Jacobian C = CurveJacobian.PicardConstruction.jacobian C := rfl
example : Jacobian.instGrpObj (C := C) =
    CurveJacobian.PicardConstruction.groupStructure C := rfl

example (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ Jacobian.ofCurve P = η[Jacobian C] :=
  Jacobian.comp_ofCurve C P

example (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! h : Jacobian C ⟶ A, f = Jacobian.ofCurve P ≫ h :=
  Jacobian.exists_unique_ofCurve_comp C P f hf

-- The map represents the normalized graph divisor, rather than an arbitrary
-- morphism satisfying only the final theorem's conclusion.
example (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (RelativePicard.degreeZeroGroupRepresentation C).homEquiv (Jacobian.ofCurve P) =
      ⟨CurveJacobian.PicardConstruction.normalizedClass C P,
        CurveJacobian.PicardConstruction.normalizedClass_degreeZero C P⟩ := by
  exact CurveJacobian.PicardConstruction.ofCurve_represents C P

end Curves

-- The bound is chosen before the field and curve are quantified.
example (g d : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (F : Type) [Field F] [NumberField F]
      (_hF : finrank ℚ F ≤ d) (C : Over (Spec (.of F))) [IsProper C.hom]
      [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
      (_hC : genus C = g),
      ENat.card (𝟙_ (Over (Spec (.of F))) ⟶ C) ≤
        B ^ (1 + freeRank (𝟙_ (Over (Spec (.of F))) ⟶ Jacobian C)) :=
  UniformMordellLang.theorem_1_1_exists g d hg hd

-- Preserve the original universe-polymorphic statement and the single constant
-- c(g,d), without introducing a chosen base point into the assumptions.
example : ∀ (g d : ℕ) (_hg : 2 ≤ g) (_hd : 1 ≤ d)
    {F : Type u} [Field F] [NumberField F] (_hF : finrank ℚ F ≤ d)
    (C : Over (Spec (.of F))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (_hC : genus C = g),
    ENat.card (𝟙_ (Over (Spec (.of F))) ⟶ C) ≤
      UniformMordellLang.c g d ^
        (1 + freeRank (𝟙_ (Over (Spec (.of F))) ⟶ Jacobian C)) :=
  @UniformMordellLang.theorem_1_1

example (g d : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d)
    {F : Type u} [Field F] [NumberField F] (hF : finrank ℚ F ≤ d)
    (C : Over (Spec (.of F))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (hC : genus C = g) :
    ENat.card (𝟙_ (Over (Spec (.of F))) ⟶ C) ≤
      UniformMordellLang.c g d ^
        (1 + freeRank (𝟙_ (Over (Spec (.of F))) ⟶ Jacobian C)) :=
  UniformMordellLang.theorem_1_1 g d hg hd hF C hC

example (g d : ℕ) : 1 ≤ UniformMordellLang.c g d :=
  UniformMordellLang.one_le_c g d

example (g d B : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d)
    (hB : UniformMordellLang.IsUniformBound g d B) :
    UniformMordellLang.c g d ≤ B :=
  UniformMordellLang.c_min g d B hg hd hB
