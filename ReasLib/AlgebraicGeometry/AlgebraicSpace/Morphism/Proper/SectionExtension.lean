module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible

/-!
# Extension of sections of proper morphisms of algebraic spaces

A section of a proper morphism over a quasi-compact open extends over the inverse
image of a larger quasi-compact open after an admissible blowup of the ambient
quasi-compact, quasi-separated algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A section of a proper morphism over a quasi-compact open extends over the
inverse image of a larger quasi-compact open after an admissible blowup of the
ambient quasi-compact, quasi-separated algebraic space. The extended section
composes with the proper morphism to the restriction of the blowup morphism. -/
theorem exists_isAdmissibleBlowup_extending_section
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (U W : OpenSubspace Y) [IsQuasiCompact U.X] [IsQuasiCompact W.X]
    (iUW : U.X ⟶ W.X) [IsOpenImmersion iUW] (hiUW : iUW ≫ W.ι = U.ι)
    (f : X ⟶ W.X) [Proper f] (s : U.X ⟶ X) (hs : s ≫ f = iUW) :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (s' : pullback b W.ι ⟶ X),
      IsAdmissibleBlowup U b ∧
        pullback.fst (pullback.snd b W.ι) iUW ≫ s' =
          pullback.snd (pullback.snd b W.ι) iUW ≫ s ∧
        s' ≫ f = pullback.snd b W.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
