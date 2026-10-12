/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- For a commutative ring `A` and positive `n`, the relative cotangent sheaf of projective
`n`-space, `n + 1` copies of `𝒪(-1)`, and the structure sheaf form a short exact sequence. -/
theorem exists_eulerSequence_shortExact
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Ω[(ProjectiveSpace.toSpec A n).toShHom] ⟶
        ∐ fun _ : Fin (n + 1) ↦ ProjectiveSpace.twistingSheaf A n (-1))
      (π : (∐ fun _ : Fin (n + 1) ↦ ProjectiveSpace.twistingSheaf A n (-1)) ⟶
        (SheafOfModules.unit (ProjectiveSpace.scheme A n).ringCatSheaf :
          (ProjectiveSpace.scheme A n).Modules))
      (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact := sorry

end AlgebraicGeometry.ProjectiveSpace
