/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Etale.Field
public import ReasLib.RingTheory.Etale.Weakly.IndEtale
public import ReasLib.RingTheory.Etale.Weakly.TensorSquare
import Mathlib.Tactic.CrossRefAttribute

/-!
# Field criteria for weakly etale algebras

This leaf owns the field-level filtered-colimit characterization and the finite-stage
consequence.  The presentation predicate is the canonical `RingHom.IndEtale`; its
representation-level `Raw` spelling is kept only at source-facing compatibility points.
@stack 092Q
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.WeaklyEtale

variable {K : Type u} {B : Type v} [Field K] [CommRing B] [Algebra K B]

/-- Every finitely generated subalgebra of a weakly etale algebra over a field is etale. -/
@[stacks 092Q "finitely generated subalgebras of weakly etale algebras"]
theorem etale_of_fg_subalgebra (h : Algebra.WeaklyEtale K B)
    (A : Subalgebra K B) (hA : A.FG) :
    Algebra.Etale K A := sorry

/-- A weakly etale algebra over a field is ind-etale. -/
@[stacks 092Q "weakly etale algebras over fields are ind-etale"]
theorem indEtale (h : Algebra.WeaklyEtale K B) :
    (algebraMap K B).IndEtale := sorry

/-- Over a field, a weakly etale algebra is exactly an ind-etale algebra map. -/
@[stacks 092Q "weakly etale and ind-etale over a field"]
theorem iff_indEtale :
    Algebra.WeaklyEtale K B ↔ (algebraMap K B).IndEtale := sorry

/-- The field-level tensor-square, weakly-etale, and ind-etale formulations are equivalent. -/
@[stacks 092Q "tensor-square weakly-etale ind-etale TFAE"]
theorem tfae :
    List.TFAE
      [ (Algebra.tensorSquareMultiplication K B).Flat,
        Algebra.WeaklyEtale K B,
        (algebraMap K B).IndEtale ] := sorry

end Algebra.WeaklyEtale
