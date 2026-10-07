module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# The affine plane quintic `x ^ 5 - 5 * x * y ^ 4 + 20 * y - 16` over `ℂ`

The spectrum of `ℂ[x, y] ⧸ (X 0 ^ 5 - 5 * X 0 * X 1 ^ 4 + 20 * X 1 - 16)`,
viewed as a variety over `ℂ`, together with the closed `ℂ`-point `(1, 1)`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.AffineQuintic

/-- The plane equation `X 0 ^ 5 - 5 * X 0 * X 1 ^ 4 + 20 * X 1 - 16` in `ℂ[x, y]`. -/
def equation : MvPolynomial (Fin 2) ℂ :=
  X 0 ^ 5 - 5 * X 0 * X 1 ^ 4 + 20 * X 1 - 16

/-- The principal relation ideal of the affine plane quintic. -/
def relationIdeal : Ideal (MvPolynomial (Fin 2) ℂ) :=
  Ideal.span {equation}

/-- The coordinate ring `ℂ[x, y] ⧸ (X 0 ^ 5 - 5 * X 0 * X 1 ^ 4 + 20 * X 1 - 16)`. -/
abbrev CoordinateRing : Type :=
  MvPolynomial (Fin 2) ℂ ⧸ relationIdeal

/-- The affine scheme `Spec (ℂ[x, y] ⧸ (X 0 ^ 5 - 5 * X 0 * X 1 ^ 4 + 20 * X 1 - 16))`. -/
def scheme : Scheme :=
  Spec (CommRingCat.of CoordinateRing)

/-- The structure morphism to `Spec ℂ` induced by `algebraMap ℂ CoordinateRing`. -/
def toBase : scheme ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ CoordinateRing))

/-- The affine plane quintic as a scheme over the field `ℂ`. -/
def over : SchemeOverField ℂ :=
  Over.mk toBase

/-- The affine plane quintic is a variety over `ℂ`. -/
instance instVariety_over : Variety over := sorry

/-- Affine coordinates of the closed `ℂ`-point `(1, 1)`. -/
def coords : Fin 2 → ℂ :=
  ![1, 1]

/-- The distinguished coordinates are `(1, 1)`. -/
theorem coords_eq : coords 0 = 1 ∧ coords 1 = 1 := sorry

/-- Evaluation of `ℂ[x, y]` at the coordinates `(1, 1)`. -/
def evalAtCoords : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ :=
  aeval coords

/-- The defining equation vanishes at `(1, 1)`. -/
theorem evalAtCoords_equation : evalAtCoords equation = 0 := sorry

/-- Polynomials in the relation ideal vanish at `(1, 1)`. -/
theorem evalAtCoords_eq_zero_of_mem (p : MvPolynomial (Fin 2) ℂ)
    (hp : p ∈ relationIdeal) : evalAtCoords p = 0 := sorry

/-- The partial derivative in `X 0` vanishes at `(1, 1)`. -/
theorem eval_pderiv_zero : eval coords (pderiv 0 equation) = 0 := sorry

/-- The partial derivative in `X 1` vanishes at `(1, 1)`. -/
theorem eval_pderiv_one : eval coords (pderiv 1 equation) = 0 := sorry

/-- Evaluation of the coordinate ring at the closed `ℂ`-point `(1, 1)`. -/
def evalCoordinateRing : CoordinateRing →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ relationIdeal evalAtCoords evalAtCoords_eq_zero_of_mem

/-- The morphism `Spec ℂ ⟶ scheme` sending the unique point of `Spec ℂ` to `(1, 1)`. -/
def pointHom : Spec (CommRingCat.of ℂ) ⟶ scheme :=
  Spec.map (CommRingCat.ofHom evalCoordinateRing.toRingHom)

/-- The rational point `(1, 1)` is a section of the structure morphism to `Spec ℂ`. -/
theorem pointHom_comp_toBase : pointHom ≫ toBase = 𝟙 _ := sorry

/-- The closed `ℂ`-point `(1, 1)` on the affine plane quintic. -/
def singularPoint : scheme :=
  pointHom.base (IsLocalRing.closedPoint ℂ)

/-- The image of `(1, 1)` is a closed point of `scheme`. -/
theorem singularPoint_mem_closedPoints : singularPoint ∈ closedPoints scheme := sorry

/-- The closed `ℂ`-point `(1, 1)` lies in the singular locus of the affine plane quintic
`Spec (ℂ[x, y] ⧸ (X 0 ^ 5 - 5 * X 0 * X 1 ^ 4 + 20 * X 1 - 16))`. -/
theorem singularPoint_mem_singularLocus : singularPoint ∈ Sing(scheme) := sorry

end AlgebraicGeometry.AffineQuintic
