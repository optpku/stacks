/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology.Naturality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Multiplication by a homogeneous quadric, as a map `O(-2) ⟶ O(0)` on `P^2`. -/
def quadricMul {k : Type u} [Field k]
    (s : MvPolynomial (Fin 3) k) (hs : s ∈ grading k 2 2) :
    twistingSheaf k 2 (-2) ⟶ twistingSheaf k 2 0 :=
  twistingSheaf.mulHomogeneous 2 (-2) 2 s hs ≫
    eqToHom (congrArg (twistingSheaf k 2) (neg_add_cancel (2 : ℤ)))

/-- The map `O_X(-2)^⊕3 ⟶ O_X` given by three homogeneous quadrics on `P^2`. -/
def threeQuadricHom (k : Type u) [Field k]
    (s : Fin 3 → MvPolynomial (Fin 3) k) (hs : ∀ i, s i ∈ grading k 2 2) :
    biproduct (fun _ : Fin 3 ↦ twistingSheaf k 2 (-2)) ⟶ twistingSheaf k 2 0 :=
  biproduct.desc fun i ↦ quadricMul (s i) (hs i)

/-- The inclusion of the `i`th summand of `O(-2)^⊕3` followed by `threeQuadricHom`
is multiplication by the `i`th quadric. -/
theorem threeQuadricHom_ι {k : Type u} [Field k]
    (s : Fin 3 → MvPolynomial (Fin 3) k) (hs : ∀ i, s i ∈ grading k 2 2)
    (i : Fin 3) :
    biproduct.ι (fun _ : Fin 3 ↦ twistingSheaf k 2 (-2)) i ≫
        threeQuadricHom k s hs =
      quadricMul (s i) (hs i) := sorry

/-- In standard projective space with `n = 2`, three homogeneous
quadrics `s 0, s 1, s 2`, viewed as global sections of `O_X(2)`, determine the
coherent sheaf `F = Coker(O_X(-2)^⊕3 ⟶ O_X)` given by multiplication by those
sections. -/
def threeQuadricCoker (k : Type u) [Field k]
    (s : Fin 3 → MvPolynomial (Fin 3) k) (hs : ∀ i, s i ∈ grading k 2 2) :
    (scheme k 2).Modules :=
  cokernel (threeQuadricHom k s hs)

/-- The cokernel of three quadric multiplications on `P^2` is coherent. -/
instance instIsCoherent_threeQuadricCoker {k : Type u} [Field k]
    (s : Fin 3 → MvPolynomial (Fin 3) k) (hs : ∀ i, s i ∈ grading k 2 2) :
    (threeQuadricCoker k s hs).IsCoherent := sorry

/- Operator-derived solution to the pinned exercise, not a list quoted from
the source. See local-error-records/0DCJ/DERIVED-CLASSIFICATION.md. The integer
division below represents the integer-valued rational polynomial on ALL ℤ;
it is not division in the field k. -/

/-- The nine numerical polynomials for cokernels of three plane quadrics,
ordered as the plane, conic, line with a point, line, and lengths zero to four. -/
def threeQuadricHilbertValues (j : Fin 9) (n : ℤ) : ℤ :=
  ![(n + 2) * (n + 1) / 2, 2 * n + 1, n + 2, n + 1, 0, 1, 2, 3, 4] j

/-- Explicit triples over every field realizing the nine listed values in order.
The length-one triple is nonmonomial and works also in characteristic two. -/
def threeQuadricWitness (k : Type u) [Field k] (j : Fin 9) :
    Fin 3 → MvPolynomial (Fin 3) k :=
  let x : MvPolynomial (Fin 3) k := MvPolynomial.X 0
  let y : MvPolynomial (Fin 3) k := MvPolynomial.X 1
  let z : MvPolynomial (Fin 3) k := MvPolynomial.X 2
  ![![0, 0, 0], ![x ^ 2, 0, 0], ![x ^ 2, x * y, 0], ![x ^ 2, x * y, x * z],
    ![x ^ 2, y ^ 2, z ^ 2], ![x * z + y ^ 2, y * z + x ^ 2, x * y],
    ![x ^ 2, y ^ 2, x * z], ![x ^ 2, x * y, y ^ 2], ![x ^ 2, y ^ 2, 0]] j

/-- Every entry of each explicit witness has homogeneous degree two, including zero. -/
theorem threeQuadricWitness_homogeneous (k : Type u) [Field k] (j : Fin 9) :
    ∀ i, threeQuadricWitness k j i ∈ grading k 2 2 := by
  intro i
  fin_cases j <;> fin_cases i <;> simp only [threeQuadricWitness]
  all_goals change MvPolynomial.IsHomogeneous _ 2
  all_goals first
    | exact MvPolynomial.isHomogeneous_zero (Fin 3) k 2
    | exact MvPolynomial.isHomogeneous_X_pow _ 2
    | exact (MvPolynomial.isHomogeneous_X k _).mul (MvPolynomial.isHomogeneous_X k _)
    | exact ((MvPolynomial.isHomogeneous_X k _).mul (MvPolynomial.isHomogeneous_X k _)).add
        (MvPolynomial.isHomogeneous_X_pow _ 2)

/-- The specified witnesses have the specified Hilbert polynomials over any field.
The sheaf/saturation/cohomology identifications are retained as genuine Prop debt. -/
theorem threeQuadricWitness_hilbertPolynomial (k : Type u) [Field k] (j : Fin 9) :
    hilbertPolynomial k 2
      (threeQuadricCoker k (threeQuadricWitness k j) (threeQuadricWitness_homogeneous k j)) =
        threeQuadricHilbertValues j := sorry

/-- Every cokernel of three degree-two sections has one of the nine values.
This is the exhaustiveness direction, including zero sections and finite fields. -/
theorem threeQuadricCoker_hilbertPolynomial_values (k : Type u) [Field k]
    (s : Fin 3 → MvPolynomial (Fin 3) k) (hs : ∀ i, s i ∈ grading k 2 2) :
    ∃ j : Fin 9, hilbertPolynomial k 2 (threeQuadricCoker k s hs) =
      threeQuadricHilbertValues j := sorry

/-- Exercise 111.45.6: over every field, the Hilbert polynomials of the actual
cokernels of three homogeneous quadrics on the projective plane are exactly
the nine explicit numerical polynomials, with every value attained over that field. -/
@[stacks 0DCJ]
theorem threeQuadricCoker_hilbertPolynomial_classification (k : Type u) [Field k]
    (P : ℤ → ℤ) :
    (∃ (s : Fin 3 → MvPolynomial (Fin 3) k) (hs : ∀ i, s i ∈ grading k 2 2),
      hilbertPolynomial k 2 (threeQuadricCoker k s hs) = P) ↔
      ∃ j : Fin 9, P = threeQuadricHilbertValues j := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact threeQuadricCoker_hilbertPolynomial_values k s hs
  · rintro ⟨j, rfl⟩
    exact ⟨threeQuadricWitness k j, threeQuadricWitness_homogeneous k j,
      threeQuadricWitness_hilbertPolynomial k j⟩

end AlgebraicGeometry.ProjectiveSpace
