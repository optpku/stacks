/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.GlobalSections
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/- Lemma 50.20.2: if `X` is smooth and proper over a field `k`, then the differential
`H⁰(X, 𝒪_X) → H⁰(X, Ω¹_{X/k})` is zero. -/
@[stacks 0FW5] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.globalSectionsDifferential_eq_zero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] [IsProper X.hom],
      ∀ a : Γ(X.left, ⊤),
        ((d[X.hom.toShHom]).app (op (⊤ : X.left.Opens))).d a = 0)

end AlgebraicGeometry.Scheme.RelativeDifferentials
