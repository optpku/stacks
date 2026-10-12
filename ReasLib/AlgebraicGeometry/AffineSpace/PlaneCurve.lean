/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.KrullDimension

/-!
# Lines, plane curves, and quadrics in the complex affine plane

This module defines polynomial equations and the associated closed subschemes
for lines, plane curves, and quadrics in the complex affine plane.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AffineSpace

/-- The first affine coordinate polynomial on the complex affine plane. -/
def xCoord : MvPolynomial (ULift (Fin 2)) ℂ :=
  X (ULift.up 0)

/-- The second affine coordinate polynomial on the complex affine plane. -/
def yCoord : MvPolynomial (ULift (Fin 2)) ℂ :=
  X (ULift.up 1)

/-- The first affine coordinate polynomial is the first standard polynomial variable. -/
theorem xCoord_eq_X : xCoord = X (ULift.up 0) := by
  rfl

/-- The second affine coordinate polynomial is the second standard polynomial variable. -/
theorem yCoord_eq_X : yCoord = X (ULift.up 1) := by
  rfl

/-- The global section of the complex affine plane associated to a polynomial. -/
def ofPolynomial (f : MvPolynomial (ULift (Fin 2)) ℂ) :
    Γ(𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ)), ⊤) :=
  (SpecIso (ULift (Fin 2)) (CommRingCat.of ℂ)).hom.appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift (Fin 2)) ℂ))).inv f)

/-- The global section associated to a coordinate polynomial is the corresponding affine coordinate. -/
theorem ofPolynomial_X (i : ULift (Fin 2)) :
    ofPolynomial (X i) = coord (Spec (CommRingCat.of ℂ)) i := sorry

/-- The closed subscheme of the complex affine plane cut out by one polynomial equation. -/
def vanishing (f : MvPolynomial (ULift (Fin 2)) ℂ) :
    (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {ofPolynomial f})

/-- The support of a polynomial vanishing subscheme is its global-section zero locus. -/
theorem vanishing_support (f : MvPolynomial (ULift (Fin 2)) ℂ) :
    ((vanishing f).support : Set (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ)))) =
      (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).zeroLocus {ofPolynomial f} := sorry

/-- The linear polynomial `a * x + b * y + c` on the complex affine plane. -/
def linearPolynomial (a b c : ℂ) : MvPolynomial (ULift (Fin 2)) ℂ :=
  C a * xCoord + C b * yCoord + C c

/-- The coefficient presentation of a linear polynomial. -/
theorem linearPolynomial_eq (a b c : ℂ) :
    linearPolynomial a b c = C a * xCoord + C b * yCoord + C c := by
  rfl

/-- The quadratic polynomial `a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f`. -/
def quadraticPolynomial (a b c d e f : ℂ) : MvPolynomial (ULift (Fin 2)) ℂ :=
  C a * xCoord ^ 2 + C b * xCoord * yCoord + C c * yCoord ^ 2 +
    C d * xCoord + C e * yCoord + C f

/-- The coefficient presentation of a quadratic polynomial. -/
theorem quadraticPolynomial_eq (a b c d e f : ℂ) :
    quadraticPolynomial a b c d e f =
      C a * xCoord ^ 2 + C b * xCoord * yCoord + C c * yCoord ^ 2 +
        C d * xCoord + C e * yCoord + C f := by
  rfl

/-- The closed subscheme cut out by a linear equation. -/
def line (a b c : ℂ) : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData :=
  vanishing (linearPolynomial a b c)

/-- The subscheme defined by a line is its polynomial vanishing subscheme. -/
theorem line_eq_vanishing (a b c : ℂ) :
    line a b c = vanishing (linearPolynomial a b c) := by
  rfl

/-- A line is a closed subscheme defined by a linear equation with nonzero linear part. -/
def IsLine (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) : Prop :=
  ∃ a b c : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ I = line a b c

/-- A closed subscheme is a line exactly when it has a nonzero linear presentation. -/
theorem isLine_iff (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) :
    IsLine I ↔ ∃ a b c : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ I = line a b c := by
  rfl

/-- A plane curve is an irreducible closed subscheme of topological Krull dimension one. -/
def IsPlaneCurve (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) : Prop :=
  IrreducibleSpace I.subscheme ∧ topologicalKrullDim I.subscheme = 1

/-- A closed subscheme is a plane curve exactly when it is irreducible of dimension one. -/
theorem isPlaneCurve_iff (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) :
    IsPlaneCurve I ↔
      IrreducibleSpace I.subscheme ∧ topologicalKrullDim I.subscheme = 1 := by
  rfl

/-- A quadric is a plane curve with a nonzero quadratic coefficient part. -/
def IsQuadric (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) : Prop :=
  IsPlaneCurve I ∧
    ∃ a b c d e f : ℂ,
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ I = vanishing (quadraticPolynomial a b c d e f)

/-- A closed subscheme is a quadric exactly when it has the specified quadratic presentation. -/
theorem isQuadric_iff (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) :
    IsQuadric I ↔
      IsPlaneCurve I ∧
        ∃ a b c d e f : ℂ,
          (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
            I = vanishing (quadraticPolynomial a b c d e f) := by
  rfl

/-- Two closed subschemes meet when their supports have nonempty intersection. -/
def Meets
    (I J : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) : Prop :=
  ((I.support : Set (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ)))) ∩ J.support).Nonempty

/-- The relation `Meets` is nonempty intersection of the underlying supports. -/
theorem meets_iff
    (I J : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) :
    Meets I J ↔
      ((I.support : Set (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ)))) ∩ J.support).Nonempty := by
  rfl

/-- Two closed subschemes meet exactly when the infimum of their supports is nonempty. -/
theorem meets_iff_support_inf
    (I J : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData) :
    Meets I J ↔ I.support ⊓ J.support ≠ ⊥ := sorry

/-- The polynomial defining the graph of the square map. -/
def graphSquarePolynomial : MvPolynomial (ULift (Fin 2)) ℂ :=
  yCoord - xCoord ^ 2

/-- The closed subscheme given by the graph equation `y - x ^ 2 = 0`. -/
def graphSquare : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData :=
  vanishing graphSquarePolynomial

/-- The square graph is the vanishing subscheme of `y - x ^ 2`. -/
theorem graphSquare_eq_vanishing :
    graphSquare = vanishing (yCoord - xCoord ^ 2) := by
  rfl

/-- The graph of the square map is a plane curve. -/
theorem graphSquare_isPlaneCurve : IsPlaneCurve graphSquare := sorry

/-- The polynomial defining the graph of the cube map. -/
def graphCubePolynomial : MvPolynomial (ULift (Fin 2)) ℂ :=
  yCoord - xCoord ^ 3

/-- The closed subscheme given by the graph equation `y - x ^ 3 = 0`. -/
def graphCube : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData :=
  vanishing graphCubePolynomial

/-- The cube graph is the vanishing subscheme of `y - x ^ 3`. -/
theorem graphCube_eq_vanishing :
    graphCube = vanishing (yCoord - xCoord ^ 3) := by
  rfl

/-- The graph of the cube map is a plane curve. -/
theorem graphCube_isPlaneCurve : IsPlaneCurve graphCube := sorry

/-- The square graph is a plane curve meeting every line in the complex affine plane. -/
theorem graphSquare_meets_every_line :
    IsPlaneCurve graphSquare ∧ ∀ I, IsLine I → Meets graphSquare I := sorry

/-- The cube graph is a plane curve meeting every line and every quadric. -/
theorem graphCube_meets_every_line_and_quadric :
    IsPlaneCurve graphCube ∧
      ∀ I, (IsLine I ∨ IsQuadric I) → Meets graphCube I := sorry

/-- Every plane curve has another plane curve with disjoint support. -/
theorem exists_disjoint_planeCurve
    (I : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData)
    (hI : IsPlaneCurve I) :
    ∃ J : (𝔸(ULift (Fin 2); Spec (CommRingCat.of ℂ))).IdealSheafData,
      IsPlaneCurve J ∧ I.support ⊓ J.support = ⊥ := sorry

end AlgebraicGeometry.AffineSpace
