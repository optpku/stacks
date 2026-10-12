/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap71.Definition_71_9_2_RelativeEffectiveCartier
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Base change of relative effective Cartier divisors on algebraic spaces

An effective Cartier divisor on an algebraic space which is flat over the base
remains effective Cartier after base change along a morphism of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor

/-- The inverse image of a relative effective Cartier divisor along the first
leg of an `IsPullback` square, with scheme base change, is an effective Cartier
divisor. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor f D.ι]
    {Y' : Over S} {X' : AlgebraicSpace S}
    {g : ofOver Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ ofOver Y'}
    (sq : IsPullback g' f' f g) :
    IsEffectiveCartierDivisor (D.inverseImage g').ι :=
  sorry

/-- The inverse image of a relative effective Cartier divisor along
`pullback.fst f g`, for a morphism of schemes `g`, is an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_inverseImage_pullback_fst
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor f D.ι] {Y' : Over S}
    (g : ofOver Y' ⟶ Y) :
    IsEffectiveCartierDivisor (D.inverseImage (pullback.fst f g)).ι :=
  sorry

/-- After scheme base change, the inverse image of a relative effective Cartier
divisor remains relative effective Cartier over the new base. -/
instance inverseImage_pullback_fst {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor f D.ι] {Y' : Over S}
    (g : ofOver Y' ⟶ Y) :
    IsRelativeEffectiveCartierDivisor (pullback.snd f g)
      (D.inverseImage (pullback.fst f g)).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsRelativeEffectiveCartierDivisor
