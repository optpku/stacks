/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Transpose.Graph

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (X Y : SchemeOverField k)
variable [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
variable [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
variable (d e : ℕ)
variable (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
variable (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞))
variable (r n : ℤ)
variable (z : CycleGroup (X ⨯ Y).left
  ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) n)
variable (f : Y ⟶ X)

/- Compatibility check for factor exchange on raw algebraic cycles. -/
#check (AlgebraicCycle.swapEquiv X Y :
  AlgebraicCycle (X ⨯ Y).left ℤ ≃+ AlgebraicCycle (Y ⨯ X).left ℤ)

/- Compatibility check for factor exchange on represented Chow classes. -/
#check (ChowGroup.swapEquiv_chowClass X Y n z :
  ChowGroup.swapEquiv X Y n
      (@chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n z) =
    @chowClass (Y ⨯ X).left
      (LocallyOfFiniteType.isLocallyNoetherian (Y ⨯ X).hom)
      ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
      (CycleGroup.mapHom (Limits.prod.braiding X Y).hom.left
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) n z))

/- Compatibility check for transpose of rational correspondences. -/
#check (Correspondence.transpose X Y d e hXdim hYdim r :
  Correspondence.Rational X Y r ≃ₗ[ℚ]
    Correspondence.Rational Y X ((d : ℤ) - (e : ℤ) + r))

/- Compatibility check for transpose of a graph correspondence. -/
#check (Correspondence.transpose_graph X Y d e hXdim hYdim f :
  Correspondence.transpose X Y d e hXdim hYdim 0
      (Correspondence.rationalGraph f) =
    Correspondence.transposedGraph X Y d e hXdim hYdim f)

end AlgebraicGeometry
