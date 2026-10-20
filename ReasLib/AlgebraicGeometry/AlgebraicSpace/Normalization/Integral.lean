module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction

/-!
# Relative normalization along integral morphisms

An integral morphism is its own relative normalization, and its canonical map
to the constructed relative normalization is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The canonical map from the source of an integral quasi-compact quasi-separated
morphism to its relative normalization is an isomorphism. -/
@[stacks 0825]
instance instIsIso_toNormalization_of_isIntegralHom
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom f] :
    IsIso (toNormalization f) :=
  sorry

/-- If `f : X ⟶ Y` is integral, then the identity factorization `f = 𝟙 X ≫ f`
exhibits `X` as a relative normalization of `Y` in `X`. -/
theorem isNormalization_id_of_isIntegralHom
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] : IsNormalization f (𝟙 X) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
