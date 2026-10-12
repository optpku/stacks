/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Lemma 38.32.1 (1): over a quasi-compact quasi-separated scheme, the category of
compactifications of a compactifiable fixed scheme is cofiltered. -/
@[stacks 0ATU] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.instIsCofiltered :
    ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (X : Over S) [Nonempty (Of S X)], IsCofiltered (Of S X))

/- Lemma 38.32.1 (2): compactifications with topologically and scheme-theoretically dense
interior form an initial full subcategory of all compactifications. -/
@[stacks 0ATU] #check
  (AlgebraicGeometry.Scheme.Compactification.DenseOf.instInitialInclusion :
    ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (X : Over S) [Nonempty (Of S X)], Functor.Initial (DenseOf.inclusion S X))

/- Lemma 38.32.1 (3): a morphism of compactifications with dense source interior pulls the
open image of the target interior back to the open image of the source interior. -/
@[stacks 0ATU] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.preimage_opensRange :
    ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (X : Over S) [Nonempty (Of S X)] {P' P : Of S X} (f : P' ⟶ P)
      [IsDominant (Of.ι P')],
      Of.ambientMap f ⁻¹ᵁ (Of.ι P).opensRange = (Of.ι P').opensRange)

end AlgebraicGeometry.Scheme.Compactification
