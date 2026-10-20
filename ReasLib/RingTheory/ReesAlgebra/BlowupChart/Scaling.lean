module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Transport
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import ReasLib.RingTheory.ReesAlgebra.Scaling

/-!
# Scaling maps of affine blowup charts

This leaf owns the canonical map induced by the principal scaling
`I ↦ (f) * I` and `a ↦ f * a`.  The construction is separated into the
underlying ring homomorphism and its `R`-algebra enhancement so that later
localization arguments can use whichever layer they need.  It is independent
of the chapter files and only uses the graded Rees-algebra and homogeneous
localization owners.

@stack 0BBI
-/

@[expose] public section

noncomputable section

universe u

open HomogeneousLocalization
open scoped AffineBlowupChart

namespace AffineBlowupChart.Scaling

variable {R : Type u} [CommRing R]

/-! ## Objects -/

/-- The affine blowup chart of the principally scaled ideal. -/
@[stacks 0BBI "scaled affine blowup chart"]
abbrev chart (I : Ideal R) (a : I) (f : R) :=
  affineBlowupChart (ReesAlgebra.Scaling.ideal I f)
    (ReesAlgebra.Scaling.element I a f)

/-- The canonical numerator `f ^ n * r` in the `n`-th power of the scaled ideal. -/
@[stacks 0BBI "scaled chart power numerator"]
def powerElement (I : Ideal R) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    ↥(ReesAlgebra.Scaling.ideal I f ^ n) :=
  ⟨f ^ n * r.1,
    (ReesAlgebra.Scaling.mem_ideal_pow_iff I f n _).2 ⟨r, rfl⟩⟩

/-- The coercion of `powerElement` is the expected scaled numerator. -/
@[stacks 0BBI "scaled chart power numerator coercion", simp]
theorem coe_powerElement (I : Ideal R) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    (powerElement I f n r : R) = f ^ n * r.1 := sorry

/-! ## The map -/

/-- The underlying ring homomorphism of the scaled chart map. -/
@[stacks 0BBI "scaled affine blowup chart ring map"]
noncomputable def toRingHom (I : Ideal R) (a : I) (f : R) :
    affineBlowupChart I a →+* chart I a f :=
  Eq.mp
    (congrArg
      (fun x : reesAlgebra (ReesAlgebra.Scaling.ideal I f) =>
        affineBlowupChart I a →+*
          Away (ReesAlgebra.Grading.grade (ReesAlgebra.Scaling.ideal I f)) x)
      (ReesAlgebra.Scaling.gradedHom_degreeOne I a f))
    (HomogeneousLocalization.Away.map
      (ReesAlgebra.Scaling.gradedHom I f)
      (ReesAlgebra.Grading.degreeOne I a))

/-- The underlying scaled chart ring map preserves the degree-zero copy of `R`. -/
@[stacks 0BBI "scaled affine blowup chart ring map on scalars", simp]
theorem toRingHom_algebraMap (I : Ideal R) (a : I) (f r : R) :
    toRingHom I a f (AffineBlowupChart.algebraMap I a r) =
      AffineBlowupChart.algebraMap
        (ReesAlgebra.Scaling.ideal I f) (ReesAlgebra.Scaling.element I a f) r := sorry

/-- The canonical `R`-algebra map from a blowup chart to its scaled chart. -/
@[stacks 0BBI "scaled affine blowup chart algebra map"]
noncomputable def map (I : Ideal R) (a : I) (f : R) :
    affineBlowupChart I a →ₐ[R] chart I a f where
  toRingHom := toRingHom I a f
  commutes' := toRingHom_algebraMap I a f

/-! ## Reusable consequences -/

/-- The canonical scaled chart map is surjective. -/
@[stacks 0BBI "scaled affine blowup chart map surjective"]
theorem surjective (I : Ideal R) (a : I) (f : R) :
    Function.Surjective (map I a f) := sorry

/-- Membership in the kernel of the scaled chart map is power torsion for the scalar `f`. -/
@[stacks 0BBI "scaled affine blowup chart kernel power criterion"]
theorem mem_ker_iff (I : Ideal R) (a : I) (f : R)
    (x : affineBlowupChart I a) :
    x ∈ RingHom.ker (map I a f).toRingHom ↔
      ∃ n : ℕ,
        (AffineBlowupChart.algebraMap I a f) ^ n * x = 0 := sorry

/-- The kernel of the scaled chart map is the primary component of the principal ideal generated
by the image of `f`. -/
@[stacks 0BBI "scaled affine blowup chart kernel primary component"]
theorem ker_eq_primaryComponent (I : Ideal R) (a : I) (f : R) :
    RingHom.ker (map I a f).toRingHom =
      (Ideal.span ({AffineBlowupChart.algebraMap I a f} :
        Set (affineBlowupChart I a))).primaryComponent (affineBlowupChart I a) := sorry

/-- The scaled chart map sends a normalized power fraction to the normalized fraction with
scaled numerator `f ^ n * r`. -/
@[stacks 0BBI "scaled affine blowup chart power fraction", simp]
theorem map_powerFraction (I : Ideal R) (a : I) (f : R) (n : ℕ)
    (r : ↥(I ^ n)) :
    map I a f (AffineBlowupChart.powerFraction I a n r) =
      AffineBlowupChart.powerFraction
        (ReesAlgebra.Scaling.ideal I f)
        (ReesAlgebra.Scaling.element I a f) n
        (powerElement I f n r) := sorry

end AffineBlowupChart.Scaling
