module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BasicOpen
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Complements of projective plane curves

An irreducible homogeneous plane form has positive degree. Its nonvanishing locus is
the complement of the projective curve, and the section algebra on this open has a
binomial upper bound on its number of generators.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- An irreducible homogeneous polynomial in three variables over a field has
positive homogeneous degree. -/
theorem zero_lt_degree_of_irreducible {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ grading k 2 d)
    (hirr : Irreducible F) : 0 < d :=
  sorry

/-- The complement of an irreducible degree-`d` projective plane curve over an
algebraically closed field is its defining basic open, whose section algebra admits
at most `Nat.choose (d + 2) 2` generators over the field. -/
theorem complement_sections {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ grading k 2 d)
    (hirr : Irreducible F) :
    ((basicOpen (R := k) 2 F : Set (scheme k 2)) =
      (ProjectiveSpectrum.zeroLocus (grading k 2)
        ({F} : Set (MvPolynomial (Fin 3) k)))ᶜ) ∧
    ∃ s : Finset (Scheme.Hom.sectionsAlgOverSpec (toSpec k 2) (basicOpen 2 F)),
      s.card ≤ Nat.choose (d + 2) 2 ∧
        Algebra.adjoin k
          (s : Set (Scheme.Hom.sectionsAlgOverSpec (toSpec k 2) (basicOpen 2 F))) = ⊤ :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
