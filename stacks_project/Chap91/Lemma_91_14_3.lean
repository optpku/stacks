module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.Derived
import StacksCheckRecall

/-! # Equivalence of coefficient pushout under the derived-coherator criterion -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 91.14.3. On a quasi-compact and quasi-separated algebraic space, pushout along
an arbitrary module map is an equivalence if its derived-coherator image is invertible. -/
@[stacks 0D3P] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension.pushout_isEquivalence :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
      [IsIso (AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension.dqMap φ)],
      Functor.IsEquivalence
        (AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension.pushoutFunctor f φ))
