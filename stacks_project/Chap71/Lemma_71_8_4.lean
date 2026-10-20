module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Presentation
import StacksCheckRecall

/-!
# Invertible modules on regular Noetherian separated algebraic spaces

On a regular Noetherian separated algebraic space, every invertible sheaf is
isomorphic to the difference sheaf of two effective Cartier divisors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory.isInvertibleObject (inverse)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.8.4: Let `S` be a scheme. Let `X` be a regular Noetherian separated
algebraic space over `S`. Then every invertible `𝒪_X`-module is isomorphic to
`𝒪_X(D - D') = 𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}` for some effective Cartier divisors
`D, D'` in `X`. Separatedness is absolute. -/
@[stacks 0DMM]
#check (AlgebraicGeometry.AlgebraicSpace.exists_iso_differenceSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsRegular X] [IsNoetherian X] [IsAbsolutelySeparated X]
    (L : X.Modules) [isInvertibleObject L],
    ∃ (D : ClosedSubspace X) (hD : IsEffectiveCartierDivisor D.ι)
      (D' : ClosedSubspace X) (hD' : IsEffectiveCartierDivisor D'.ι),
      Nonempty (L ≅ @ClosedSubspace.differenceSheaf S X D D' hD hD'))

/- The difference sheaf `𝒪_X(D - D')` is isomorphic to
`𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}`. -/
#check (AlgebraicGeometry.AlgebraicSpace.differenceSheaf_iso_tensor_inverse :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D D' : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    [IsEffectiveCartierDivisor D'.ι],
    Nonempty
      (ClosedSubspace.differenceSheaf D D' ≅
        ClosedSubspace.associatedSheaf D ⊗
          inverse (ClosedSubspace.associatedSheaf D')))

end AlgebraicGeometry.AlgebraicSpace
