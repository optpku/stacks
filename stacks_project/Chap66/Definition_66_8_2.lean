/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_8_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Topology

universe u

/- Definition 66.8.2: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `E ⊂ |X|` be a subset. We say `E` is étale locally constructible if the
equivalent conditions of Lemma 66.8.1 are satisfied. If `X` is representable this
is ordinary local constructibility on the scheme. -/
@[stacks 0ECU]
#check (AlgebraicGeometry.AlgebraicSpace.IsEtaleLocallyConstructible :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, Set (Points X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isEtaleLocallyConstructible_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)),
      List.TFAE [IsEtaleLocallyConstructible E, IsEtaleLocallyConstructible.forallAffine E,
        IsEtaleLocallyConstructible.existsSurjective E])

#check (AlgebraicGeometry.AlgebraicSpace.IsEtaleLocallyConstructible.ofOver_iff :
    ∀ {S : Scheme.{u}} {T : Over S} (E : Set (Points (ofOver T))),
      IsEtaleLocallyConstructible E ↔ IsLocallyConstructible (ofOver.pointsEquiv T ⁻¹' E))
