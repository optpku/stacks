/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Proposition 38.37.9: A type-valued presheaf on a chosen big h-site slice is
an h-sheaf if and only if it satisfies Zariski descent, affine
flat-proper-surjective equalizer descent, and affine almost-blowup descent. -/
@[stacks 0EVF] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.iffZariskiAndFlatProperAlmostBlowup :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
        (F : (Over S)ᵒᵖ ⥤ Type w),
      Presheaf.IsSheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S) F ↔
        Presheaf.IsSheaf
            (AlgebraicGeometry.ChosenBigHSite.bigZariskiTopology Schh S) F ∧
          AlgebraicGeometry.ChosenBigHSite.Equalizer.IsAffineFlatProperSurjective
              Schh S F ∧
            AlgebraicGeometry.ChosenBigHSite.AlmostBlowup.IsAffineDescent Schh S F)
