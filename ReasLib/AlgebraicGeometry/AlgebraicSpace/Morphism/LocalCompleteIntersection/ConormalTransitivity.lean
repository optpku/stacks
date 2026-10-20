module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Transitivity

/-!
# Conormal transitivity for local complete intersection morphisms of algebraic spaces

For formally unramified morphisms `Z ⟶ Y ⟶ X` of algebraic spaces over a
scheme `S`, if `Z ⟶ Y` is a local complete intersection, the canonical
conormal transitivity sequence is short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
namespace Transitivity

variable {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
variable (i : Z ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
variable [FormallyUnramified i] [IsLocalCompleteIntersection i]
variable (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X))

/-- For formally unramified morphisms `Z ⟶ Y ⟶ X` of algebraic spaces over a
scheme, if `Z ⟶ Y` is a local complete intersection, the canonical conormal
transitivity sequence `0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`, with maps
`baseChange` and `projection`, is short exact. -/
theorem shortExact_of_isLocalCompleteIntersection :
    (complex iZ fZ iY fY i sq).ShortExact :=
  sorry

/-- For formally unramified `Z ⟶ Y ⟶ X` with `Z ⟶ Y` a local complete
intersection, the comparison `baseChange` is a monomorphism. -/
instance mono_baseChange : Mono (baseChange iZ fZ iY fY i sq) :=
  (shortExact_of_isLocalCompleteIntersection iZ fZ iY fY i sq).mono_f

end Transitivity
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
