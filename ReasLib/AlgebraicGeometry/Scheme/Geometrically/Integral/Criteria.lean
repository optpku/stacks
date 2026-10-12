/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Integral

/-!
# Affine geometric-integrality criteria

The finite-extension and algebraic-closure tests for an affine algebra are
shared criteria, not chapter-local proof scaffolding. Since the scheme-level
owner `Spec.map` is universe-homogeneous, the field extensions live in the
same universe as the affine coordinate algebra. Tensor products consistently
place the coordinate algebra on the left.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SchemeOverField
namespace GeometricallyIntegral

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.49.3 (Tag 0FWF), clauses `(1) ↔ (2)`: geometric integrality can be checked after
tensoring with every finite field extension of the base. -/
@[stacks 0FWF]
theorem iff_isDomain_finiteExtension :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        IsDomain (S ⊗[k] K) := sorry

/-- Lemma 10.49.3 (Tag 0FWF), clauses `(1) ↔ (3)`: geometric integrality can be checked after
base change to the algebraic closure. -/
@[stacks 0FWF]
theorem iff_isDomain_algebraicClosure :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      IsDomain (S ⊗[k] AlgebraicClosure k) := sorry

end GeometricallyIntegral
end AlgebraicGeometry.SchemeOverField
