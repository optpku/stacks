/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FieldExtension

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 33.30.3: let `k' / k` be a field extension. Let `X` be a scheme over `k` such that `X`
is quasi-compact and quasi-separated, and `Γ(X, ⊤)` is semilocal, for example when
`Γ(X, ⊤)` is finite-dimensional over `k`. Then the pullback map `Pic(X) → Pic(X_{k'})` is
injective. -/
@[stacks 0CC5] #check
  (AlgebraicGeometry.FieldExtension.picardPullback_injective :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      [Finite (MaximalSpectrum (Γ(X, ⊤)))],
      Function.Injective
        (Scheme.Hom.picardPullback (FieldExtension.toSource k k' f)))
