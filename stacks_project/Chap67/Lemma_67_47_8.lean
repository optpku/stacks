module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Birational
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 67.47.8: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`
with `|X|` and `|Y|` irreducible. Then `X` and `Y` are birational if and only if there
are nonempty open subspaces `U ⊂ X` and `V ⊂ Y` which are isomorphic as algebraic
spaces over `S`. -/
@[stacks 0EMU] #check (AlgebraicGeometry.AlgebraicSpace.birational_iff_nonempty_open :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [AlgebraicSpace.IsIrreducible X] [AlgebraicSpace.IsIrreducible Y],
    AlgebraicSpace.Birational X Y ↔
      ∃ (U : AlgebraicSpace.smallZariskiSite X) (V : AlgebraicSpace.smallZariskiSite Y)
        (e : CategoryTheory.Iso U.left V.left),
        Nonempty (AlgebraicSpace.Points U.left) ∧ Nonempty (AlgebraicSpace.Points V.left))
