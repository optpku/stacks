/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.GeometricRegularity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed Unions and Geometric Regularity

This leaf records the directed-subfield descent principle for geometric
regularity.  It belongs to `Algebra.IsGeometricallyRegular`, not to the
chapter where it is first proved.

@stack 07QG
-/

@[expose] public section

namespace Algebra.IsGeometricallyRegular

universe u v w

/-- Lemma 10.166.5, tag `07QG`: if a field `k` is the directed union of subfields `kᵢ`
and a commutative algebra `A` is geometrically regular over every `kᵢ`, then `A` is
geometrically regular over `k`. -/
@[stacks 07QG]
theorem of_directed_iSup_subfields
    {k : Type u} {A : Type v} {ι : Type w}
    [Field k] [CommRing A] [Algebra k A] [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (hA : ∀ i, IsGeometricallyRegular (kᵢ i) A) :
    IsGeometricallyRegular k A := sorry

end Algebra.IsGeometricallyRegular
