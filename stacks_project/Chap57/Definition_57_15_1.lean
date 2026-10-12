/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap57.Definition_57_15_1_Kernel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Definition 57.15.1: for smooth proper morphisms `X → S` and `Y → S`, a
perfect derived object `K` on `X ×_S Y` is the Fourier--Mukai kernel of a
relative equivalence from `X` to `Y` over `S` if and only if there exists a
perfect inverse kernel `K'` on `Y ×_S X` whose derived convolutions recover
the relative diagonals `Δ_{X/S,*} 𝒪_X` and `Δ_{Y/S,*} 𝒪_Y`. Equivalently,
the isomorphism class of `K` is invertible in the category of Section 57.14. -/
@[stacks 0G0I]
theorem isRelativeEquivalenceKernel_iff {S : Scheme.{u}}
    {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) :
    FourierMukaiObject.IsRelativeEquivalenceKernel K ↔
      ∃ K' : @RingedSpace.ModuleDerived.Perfect
          (Limits.pullback Y.hom X.hom).toRingedSpace,
        CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel X Y X K K')
            (FourierMukaiObject.diagonalKernel X) ∧
          CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel Y X Y K' K)
            (FourierMukaiObject.diagonalKernel Y) := sorry
