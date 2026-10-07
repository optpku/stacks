module

public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.Homology
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Vanishing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy lifting from supported K-projective complexes

The generic theorem is stated for a K-projective source.  The `ProjectiveMinus` companion is the
bounded-above termwise-projective specialization used by the textbook application.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace IsKProjective

/-- A map from a K-projective complex supported in degrees `≥ n` lifts up to homotopy through a
map which is an isomorphism on cohomology above `n` and an epimorphism at `n`. -/
@[stacks 064E "K-projective homotopy lift"]
theorem existsHomotopyLift {P E L : CochainComplex A ℤ} [P.IsKProjective]
    (f : E ⟶ L) (g : P ⟶ L) (n : ℤ) (hP : P.IsStrictlyGE n)
    (h_iso : HomologyMap.IsIsoAbove f n) (h_epi : HomologyMap.IsEpiAt f n) :
    ∃ l : P ⟶ E, Nonempty (Homotopy (l ≫ f) g) := sorry

end IsKProjective

namespace ProjectiveMinus

/-- A map from a bounded-above complex of projective objects supported in degrees `≥ n` lifts up
to homotopy through a map which is an isomorphism on cohomology above `n` and an epimorphism at
`n`. -/
@[stacks 064E "bounded projective homotopy lift"]
theorem existsHomotopyLift (P : ProjectiveMinus A) {E L : CochainComplex A ℤ}
    (f : E ⟶ L) (g : (P : CochainComplex A ℤ) ⟶ L) (n : ℤ)
    (hP : (P : CochainComplex A ℤ).IsStrictlyGE n)
    (h_iso : HomologyMap.IsIsoAbove f n) (h_epi : HomologyMap.IsEpiAt f n) :
    ∃ l : (P : CochainComplex A ℤ) ⟶ E, Nonempty (Homotopy (l ≫ f) g) := sorry

end ProjectiveMinus

end CochainComplex
