module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Affine

/-!
# Frobenius counterexample for fpqc descent of differentials

The p-power map between affine lines over the prime field gives a concrete fpqc family on which
relative differential sections fail the equalizer condition.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/-- The target affine line `U = Spec (ZMod p)[u]`. -/
def affineLineU (p : ℕ) : Scheme :=
  Spec (CommRingCat.of (Polynomial (ZMod p)))

/-- The source affine line `V = Spec (ZMod p)[v]`. -/
def affineLineV (p : ℕ) : Scheme :=
  Spec (CommRingCat.of (Polynomial (ZMod p)))

/-- The structure map `U ⟶ Spec (ZMod p)`. -/
def affineLineUProjection (p : ℕ) :
    affineLineU p ⟶ Spec (CommRingCat.of (ZMod p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (Polynomial (ZMod p))))

/-- The structure map `V ⟶ Spec (ZMod p)`. -/
def affineLineVProjection (p : ℕ) :
    affineLineV p ⟶ Spec (CommRingCat.of (ZMod p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (Polynomial (ZMod p))))

/-- The polynomial ring map sending the coordinate `X` to `X ^ p`. -/
def frobeniusPolynomialMap (p : ℕ) :
    Polynomial (ZMod p) →+* Polynomial (ZMod p) :=
  Polynomial.eval₂RingHom (Polynomial.C : ZMod p →+* Polynomial (ZMod p))
    (Polynomial.X ^ p)

/-- The affine-line scheme morphism induced by `X ↦ X ^ p`. -/
def frobeniusAffineLineSchemeMap (p : ℕ) :
    affineLineV p ⟶ affineLineU p :=
  Spec.map (CommRingCat.ofHom (frobeniusPolynomialMap p))

/-- The Frobenius polynomial map commutes with the affine-line structure map. -/
theorem frobeniusAffineLineSchemeMap_over (p : ℕ) :
    frobeniusAffineLineSchemeMap p ≫ affineLineUProjection p = affineLineVProjection p := sorry

/-- The map of affine lines over `Spec (ZMod p)` induced by `X ↦ X ^ p`. -/
def frobeniusAffineLineMap (p : ℕ) :
    Over.mk (affineLineVProjection p) ⟶ Over.mk (affineLineUProjection p) :=
  Over.homMk (frobeniusAffineLineSchemeMap p) (frobeniusAffineLineSchemeMap_over p)

/-- The singleton p-power family of affine lines is an fpqc covering. -/
theorem frobeniusAffineLine_fpqcCover (p : ℕ) [Fact p.Prime] :
    Scheme.FpqcCovering (fun _ : Unit ↦ Over.mk (frobeniusAffineLineMap p).left) := sorry

/-- Restriction along the p-power affine-line map is zero on relative differentials. -/
theorem frobeniusAffineLine_restriction_zero (p : ℕ) [Fact p.Prime] :
    (differentialFormsPresheaf (Spec (CommRingCat.of (ZMod p)))).map
        (frobeniusAffineLineMap p).op = 0 := sorry

/-- The singleton p-power presieve does not satisfy the sheaf condition. -/
theorem frobeniusAffineLine_not_isSheafFor (p : ℕ) [Fact p.Prime] :
    ¬ Presieve.IsSheafFor
      (differentialFormsPresheaf (Spec (CommRingCat.of (ZMod p))) ⋙
        CategoryTheory.forget AddCommGrpCat)
      (Presieve.singleton (frobeniusAffineLineMap p)) := sorry

/-- The relative differential presheaf is not a sheaf for the fpqc topology. -/
theorem differentialFormsPresheaf_not_isSheaf_fpqc (p : ℕ) [Fact p.Prime] :
    ¬ Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (CommRingCat.of (ZMod p))))
      (differentialFormsPresheaf (Spec (CommRingCat.of (ZMod p))) ⋙
        CategoryTheory.forget AddCommGrpCat) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
