module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Fpqc
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Example 59.15.7 (1): the presheaf `T/S ↦ Γ(T, Ω[T/S])` on `(Over S)ᵒᵖ`. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf :
    ∀ (S : Scheme.{u}),
      (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})

/- Example 59.15.7 (2): this presheaf is a sheaf for the Zariski topology. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf_isSheaf_zariski :
    ∀ (S : Scheme.{u}),
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
        (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf S ⋙
          CategoryTheory.forget AddCommGrpCat))

/- Example 59.15.7 (3): the affine-line morphism over `Spec (ZMod p)` is induced by Frobenius. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLineMap :
    ∀ (p : ℕ),
      Over.mk
          (AlgebraicGeometry.Scheme.RelativeDifferentials.affineLineVProjection p) ⟶
        Over.mk
          (AlgebraicGeometry.Scheme.RelativeDifferentials.affineLineUProjection p))

/- Example 59.15.7 (3): the singleton Frobenius family is an fpqc covering. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLine_fpqcCover :
    ∀ (p : ℕ), [Fact p.Prime] →
      Scheme.FpqcCovering
        (fun _ : Unit ↦
          Over.mk
            (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLineMap p).left))

/- Example 59.15.7 (4): restriction along Frobenius is the zero map on differentials. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLine_restriction_zero :
    ∀ (p : ℕ), [Fact p.Prime] →
      (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf
          (Spec (CommRingCat.of (ZMod p)))).map
        (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLineMap p).op = 0)

/- Example 59.15.7 (4): the singleton Frobenius presieve does not satisfy the sheaf condition. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLine_not_isSheafFor :
    ∀ (p : ℕ), [Fact p.Prime] →
      ¬ Presieve.IsSheafFor
        (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf
            (Spec (CommRingCat.of (ZMod p))) ⋙
          CategoryTheory.forget AddCommGrpCat)
        (Presieve.singleton
          (AlgebraicGeometry.Scheme.RelativeDifferentials.frobeniusAffineLineMap p)))

/- Example 59.15.7 (5): the presheaf is not a sheaf for the fpqc topology. -/
@[stacks 03O2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf_not_isSheaf_fpqc :
    ∀ (p : ℕ), [Fact p.Prime] →
      ¬ Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (CommRingCat.of (ZMod p))))
        (AlgebraicGeometry.Scheme.RelativeDifferentials.differentialFormsPresheaf
            (Spec (CommRingCat.of (ZMod p))) ⋙
          CategoryTheory.forget AddCommGrpCat))
