/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing from K-projective complexes

This file records the orthogonality supplied by a K-projective source whose terms start above
the homological support of the target.  The core statements use independent source and target
bounds; the homology-facing statements specialize them to the adjacent bounds used most often
in applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v u

namespace CochainComplex.IsKProjective.Vanishing

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism in the homotopy category from a K-projective complex strictly supported in
degrees `≥ a` to a complex with homology supported in degrees `≤ b` is zero when `b < a`. -/
theorem homotopyOfBounds {P K : CochainComplex A ℤ} [P.IsKProjective]
    (a b : ℤ) (hab : b < a) (hP : P.IsStrictlyGE a) (hK : K.IsLE b)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj K) :
    f = 0 := sorry

/-- Stacks 064D (1): if a K-projective complex is strictly supported in degrees `≥ n` and
the target has zero homology in degrees `≥ n`, every morphism between them in the homotopy
category is zero. -/
@[stacks 064D "homotopy-category vanishing"]
theorem homotopy {P K : CochainComplex A ℤ} [P.IsKProjective]
    (n : ℤ) (hP : P.IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj K) :
    f = 0 := sorry

/-- A morphism in the derived category from a K-projective complex strictly supported in
degrees `≥ a` to a complex with homology supported in degrees `≤ b` is zero when `b < a`. -/
theorem derivedOfBounds [HasDerivedCategory.{w} A]
    {P K : CochainComplex A ℤ} [P.IsKProjective]
    (a b : ℤ) (hab : b < a) (hP : P.IsStrictlyGE a) (hK : K.IsLE b)
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K) :
    f = 0 := sorry

/-- Stacks 064D (2): if a K-projective complex is strictly supported in degrees `≥ n` and
the target has zero homology in degrees `≥ n`, every morphism between them in the derived
category is zero. -/
@[stacks 064D "derived-category vanishing"]
theorem derived [HasDerivedCategory.{w} A]
    {P K : CochainComplex A ℤ} [P.IsKProjective]
    (n : ℤ) (hP : P.IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K) :
    f = 0 := sorry

end CochainComplex.IsKProjective.Vanishing
