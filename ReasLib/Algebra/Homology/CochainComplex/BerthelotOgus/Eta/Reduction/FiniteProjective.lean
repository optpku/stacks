/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.FiniteLocallyFree
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Pair.FiniteProjective
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite

/-!
# Finite-projective terms of the reduced eta complex

Under a principal eta determinantal ideal, the corresponding eta term is finite locally free.
Reduction modulo `(f)` therefore produces a finite projective source for the reduced visible-power
pair map, whose two target factors are finite projective as well.
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Nat.Reduction

open CochainComplex.BerthelotOgus.Nat.Pair
open CochainComplex.BerthelotOgus.Nat.Reduction.Pair

variable {A : Type u} [CommRing A]

/-- A reduced eta term is finite over `A / (f)` when its eta determinantal ideal is principal. -/
theorem term_finite_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.Finite (A ⧸ principalIdeal f) ((complex f K).X i) := sorry

/-- A reduced eta term is projective over `A / (f)` when its eta determinantal ideal is
principal. -/
theorem term_projective_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.Projective (A ⧸ principalIdeal f) ((complex f K).X i) := sorry

/-- The reduced visible-power pair map is a split monomorphism under the principal eta
determinantal-ideal hypothesis. -/
theorem reducedPairLinear_isSplitMono_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (reducedPairLinear f K i)) := sorry

end CochainComplex.BerthelotOgus.Nat.Reduction
