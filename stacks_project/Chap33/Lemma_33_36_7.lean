/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Frobenius

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/-!
Lemma 33.36.7 records the neutral Frobenius differential-comparison API. The construction, its
sectionwise specification, and the characteristic-`p` isomorphism instance are owned by
`AlgebraicGeometry.Scheme.Hom` so that later applications do not depend on a chapter file.
-/

/- Lemma 33.36.7: let `p > 0` be a prime number. Let `S` be a scheme in characteristic `p`. Let
`X` be a scheme over `S`. Then the canonical comparison map
`Ω[f.toShHom] ⟶ Ω[(Scheme.Hom.relativeFrobenius f).toShHom]` attached to the relative
Frobenius `X ⟶ X^(p) = pullback f (Scheme.absoluteFrobenius p S)` is an isomorphism. -/
@[stacks 0CCC]
#check (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusDifferentialComparison_isIso :
  ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}}
    [Scheme.IsCharP S p] (f : X ⟶ S),
    IsIso (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusDifferentialComparison (p := p) f))
#check AlgebraicGeometry.Scheme.Hom.relativeFrobeniusDifferentialComparison
#check AlgebraicGeometry.Scheme.Hom.relativeFrobeniusDifferentialComparisonSpec

end
