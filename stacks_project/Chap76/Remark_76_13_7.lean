/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting.EtaleSurjective
import StacksCheckRecall

/-!
# Tempting equivalence for formal smoothness after étale-on-top

In the situation of Lemma 76.13.6 it is tempting to conclude
`FormallySmooth b ↔ FormallySmooth (a ≫ b)`. The forward implication holds;
the converse is not claimed and is likely false. The actual converse content
of the previous lemma is étale affine local lifting, not `FormallySmooth b`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over

universe u

/- Remark 76.13.7 (1): In the situation of Lemma 76.13.6, if `a : F ⟶ G` is a
representable, surjective, and étale transformation of functors on
`(Sch/S)_fppf` and `b : G ⟶ H` is formally smooth, then `a ≫ b` (source
`b ∘ a`) is formally smooth. This is the true direction of the tempting
equivalence `FormallySmooth b ↔ FormallySmooth (a ≫ b)`. -/
@[stacks 04CZ]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.precomp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        FormallySmooth b → FormallySmooth (a ≫ b))

/- Remark 76.13.7 (2): The converse `FormallySmooth (a ≫ b) → FormallySmooth b`
is not claimed and is likely not true in general; there is no
`FormallySmooth.of_precomp`. The actual converse content of Lemma 76.13.6 is
that formal smoothness of `a ≫ b` (source `b ∘ a`) yields étale affine local
lifts against an affine first-order thickening, not global formal smoothness
of `b`. -/
@[stacks 04CZ]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.exists_etaleAffineLocalLift :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        ∀ [FormallySmooth (a ≫ b)] {T T' : Over S} [IsAffine T.left]
          [IsAffine T'.left] (i : T ⟶ T') [IsFirstOrderThickening i.left]
          (x : G.obj (op T)) (y : H.obj (op T')),
          b.app (op T) x = H.map (op i) y →
            ∀ t : T.left, ∃ (U' : Over S) (π : U' ⟶ T') (z : G.obj (op U')),
              FormallySmooth.IsEtaleAffineLocalLift b i π x y z t)
