/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line
public import Mathlib.Order.KrullDimension

/-!
# Avoiding closed subsets with projective lines

This file records existence and open-sweeping results for projective lines through a closed
point that avoid an irreducible closed subset of codimension at least two.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Through a closed point outside an irreducible closed subset of codimension at least two,
there is a projective line disjoint from that subset. -/
theorem exists_avoiding
    (B : IrreducibleCloseds (ProjectiveSpace.VectorSpace.scheme k V))
    (hB : (2 : ℕ∞) ≤ Order.coheight B)
    (p : ProjectiveSpace.VectorSpace.scheme k V)
    (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)))
    (hpB : p ∉ (B : Set (ProjectiveSpace.VectorSpace.scheme k V))) :
    ∃ ℓ : ProjectiveSpace.VectorSpace.Line k V,
      p ∈ ℓ.carrier ∧
        ℓ.carrier ∩ (B : Set (ProjectiveSpace.VectorSpace.scheme k V)) = ∅ := sorry

/-- The closed points swept out by projective lines through a fixed closed point and avoiding
an irreducible closed subset of codimension at least two contain a nonempty open subset. -/
theorem exists_open_coveredBy_avoiding
    (B : IrreducibleCloseds (ProjectiveSpace.VectorSpace.scheme k V))
    (hB : (2 : ℕ∞) ≤ Order.coheight B)
    (p : ProjectiveSpace.VectorSpace.scheme k V)
    (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)))
    (hpB : p ∉ (B : Set (ProjectiveSpace.VectorSpace.scheme k V))) :
    ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
      ∀ q : ProjectiveSpace.VectorSpace.scheme k V,
        IsClosed ({q} : Set (ProjectiveSpace.VectorSpace.scheme k V)) → q ∈ U →
          ∃ ℓ : ProjectiveSpace.VectorSpace.Line k V,
            p ∈ ℓ.carrier ∧ q ∈ ℓ.carrier ∧
              ℓ.carrier ∩ (B : Set (ProjectiveSpace.VectorSpace.scheme k V)) = ∅ := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line
