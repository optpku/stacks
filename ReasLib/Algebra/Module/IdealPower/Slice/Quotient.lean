/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Slice
public import ReasLib.Algebra.Module.IdealPower.Quotient.Hom

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.PowerSlice

variable {A : Type u} [CommRing A]

/-- The slice `I ^ q / I ^ (q + m)`, bundled over the quotient ring `A ⧸ I ^ m`. -/
abbrev stageOver (I : Ideal A) (q m : ℕ) : ModuleCat.{u} (A ⧸ I ^ m) :=
  Ideal.PowerQuotient.stageOver I
    (Ideal.PowerSubmodule.stageObj I (ModuleCat.of A A) q) m

/-- The slice `I ^ q / I ^ (q + m)`, regarded as a module over `A ⧸ I ^ e`
when `m ≤ e`. -/
abbrev stageOverAt (I : Ideal A) (q m e : ℕ) (h : m ≤ e) :
    ModuleCat.{u} (A ⧸ I ^ e) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.factorPow I h)).obj (stageOver I q m)

/-- The canonical `A ⧸ I ^ n`-linear map
`I ^ n / I ^ (2 * n) ⟶ I ^ r / I ^ (2 * r)` for `r ≤ n`. -/
noncomputable def diagonalTransition (I : Ideal A) (n r : ℕ) (h : r ≤ n) :
    stageOver I n n ⟶ stageOverAt I r r n h :=
  Ideal.PowerQuotient.Hom.lift I
    (Ideal.PowerSubmodule.stageObj I (ModuleCat.of A A) n) (stageOverAt I r r n h)
    (ModuleCat.ofHom
      ((mk I A r r).comp
        (Submodule.inclusion (Ideal.PowerSubmodule.stage_antitone I h))))

/-- The diagonal transition sends a representative in `I ^ n` to its class in
`I ^ r / I ^ (2 * r)`. -/
theorem diagonalTransition_mk (I : Ideal A) (n r : ℕ) (h : r ≤ n)
    (x : Ideal.PowerSubmodule.stage I A n) :
    (diagonalTransition I n r h).hom (mk I A n n x) =
      mk I A r r
        (Submodule.inclusion (Ideal.PowerSubmodule.stage_antitone I h) x) := sorry

end Ideal.PowerSlice
