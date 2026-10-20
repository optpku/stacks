module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Coproduct

/-!
# The doubled-origin fpqc counterexample

This module constructs the singleton coproduct family over countably infinite affine space with
its origin doubled and records its local neighborhood behavior and failure to be an fpqc covering.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.FpqcCounterexample

variable (k : Type u) [Field k]

/-- The family consisting of the first canonical chart of countably infinite affine space with
its origin doubled and the spectrum of the local ring at the origin of the second chart. -/
noncomputable def family :
    Fin 2 → Over (scheme (ULift.{u} ℕ) k)
  | 0 => Over.mk (chart (ULift.{u} ℕ) k 0).ι
  | 1 =>
      Over.mk
        (((chart (ULift.{u} ℕ) k 1).toScheme).fromSpecStalk
            ((chartIso (ULift.{u} ℕ) k 1).inv.base
              (PuncturedAffineSpace.origin (ULift.{u} ℕ) k)) ≫
          (chart (ULift.{u} ℕ) k 1).ι)

/-- The singleton family obtained by taking the coproduct of the two morphisms in `family`. -/
noncomputable def singletonFamily :
    PUnit → Over (scheme (ULift.{u} ℕ) k) :=
  (FormalCoproduct.Over.coproductSingleton
    (FormalCoproduct.mk _ (family k))).obj

/-- The singleton coproduct family satisfies the pointwise finite quasi-compact neighborhood
criterion. -/
theorem neighborhood :
    Scheme.Fpqc.Criterion.Neighborhood (singletonFamily k) := sorry

/-- The singleton coproduct family is not an fpqc covering. -/
theorem not_fpqcCovering :
    ¬ Scheme.FpqcCovering (singletonFamily k) := sorry

/-- The singleton coproduct family satisfies the neighborhood criterion but is not an fpqc
covering. -/
theorem neighborhood_and_not_fpqcCovering :
    Scheme.Fpqc.Criterion.Neighborhood (singletonFamily k) ∧
      ¬ Scheme.FpqcCovering (singletonFamily k) :=
  ⟨neighborhood k, not_fpqcCovering k⟩

end AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.FpqcCounterexample
