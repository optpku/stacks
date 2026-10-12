/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Reduction.FiniteProjective
public import ReasLib.LinearAlgebra.ProductRange.SplittingLocus

/-!
# Degreewise decomposition ideals for eta reduction

The reduced eta pair has a canonical product-splitting locus ideal.  The datum itself is defined
without finiteness, regularity, or principality assumptions.  Those hypotheses occur only in the
theorems asserting the universal base-change property and finite generation.
@stack 0GSW
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors

noncomputable section

universe u v w

namespace CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition

open CochainComplex.BerthelotOgus.Nat.Reduction.Pair

variable {A : Type u} [CommRing A]

/-- The canonical ideal cutting out the product-splitting locus of the degree-`i` reduced eta
pair.  It is defined directly from the pair map and carries no proof parameters. -/
@[stacks 0GSW "degreewise eta decomposition ideal"]
noncomputable def degreeIdeal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) :
    Ideal (A ⧸ principalIdeal f) :=
  LinearMap.ProductRange.locusIdeal (reducedPairLinear f K i)

/-- An algebra kills the degreewise decomposition ideal exactly when the base-changed reduced
eta pair identifies its source with a product of submodules. -/
@[stacks 0GSW "universal property of the eta decomposition ideal"]
theorem degreeIdeal_le_ker_iff
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal)
    (B : Type w) [CommRing B] [Algebra (A ⧸ principalIdeal f) B] :
    degreeIdeal f K i ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (reducedPairLinear f K i).baseChangeIdentifiesWithProdSubmodules B := sorry

/-- Under the degree-local finite-free and principal-ideal hypotheses, the canonical
decomposition ideal is finitely generated. -/
@[stacks 0GSW "finite generation of the eta decomposition ideal"]
theorem degreeIdeal_fg
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    (degreeIdeal f K i).FG := sorry

/-- The decomposition ideal is zero exactly when the original reduced pair already has
product-shaped image. -/
theorem degreeIdeal_eq_bot_iff
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    degreeIdeal f K i = ⊥ ↔ (reducedPairLinear f K i).identifiesWithProdSubmodules := sorry

/-- If the source term of the original complex is zero, its degreewise decomposition ideal is
zero. -/
theorem degreeIdeal_eq_bot_of_isZero
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (hK : IsZero (K.X i)) : degreeIdeal f K i = ⊥ := sorry

end CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition
