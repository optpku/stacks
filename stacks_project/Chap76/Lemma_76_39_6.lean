module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Proper.SectionExtension
import StacksCheckRecall

/-!
# Extension of sections of proper morphisms of algebraic spaces

A section of a proper morphism of algebraic spaces over a nested
quasi-compact open extends after a `U`-admissible blowup of the ambient
qcqs algebraic space.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.39.6: Let `S` be a scheme. Let `X`, `Y` be algebraic spaces over
`S`. Let `U ⊂ W ⊂ Y` be open subspaces. Let `f : X ⟶ W.X` and
`s : U.X ⟶ X` be morphisms such that `s ≫ f` is the inclusion
`U.X ⟶ W.X`. Assume `f` is proper, `Y` is quasi-compact and quasi-separated,
and `U` and `W` are quasi-compact. Then there exists a `U`-admissible blowup
`b : Y' ⟶ Y` and a morphism `s' : pullback b W.ι ⟶ X` extending `s` with
`s' ≫ f = pullback.snd b W.ι`. -/
@[stacks 0CPI]
#check (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_extending_section :
    ∀
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (U W : OpenSubspace Y) [IsQuasiCompact U.X] [IsQuasiCompact W.X]
    (iUW : U.X ⟶ W.X) [IsOpenImmersion iUW] (hiUW : iUW ≫ W.ι = U.ι)
    (f : X ⟶ W.X) [Proper f] (s : U.X ⟶ X) (hs : s ≫ f = iUW),
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (s' : pullback b W.ι ⟶ X),
      IsAdmissibleBlowup U b ∧
        pullback.fst (pullback.snd b W.ι) iUW ≫ s' =
          pullback.snd (pullback.snd b W.ι) iUW ≫ s ∧
        s' ≫ f = pullback.snd b W.ι)

end AlgebraicGeometry.AlgebraicSpace
