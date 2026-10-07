module

public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_8_Normalization

/-!
# Integral morphisms of algebraic spaces are their own relative normalization

If `f : X ⟶ Y` is an integral morphism of algebraic spaces, then the canonical
map `toNormalization f : X ⟶ Hom.normalization f` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 67.48.10: let `S` be a scheme. Let `f : X ⟶ Y` be an integral morphism
of algebraic spaces over `S`. Then the integral closure of `Y` in `X` is equal
to `X`; equivalently, `toNormalization f : X ⟶ Hom.normalization f` is an
isomorphism.

In Stacks language, `f : Y ⟶ X` and the integral closure of `X` in `Y` are
Lean `f : X ⟶ Y` and `Hom.normalization f`. The quasi-compact and
quasi-separated binders are those already required to form
`Hom.toNormalization f`. -/
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

end Hom

end AlgebraicGeometry.AlgebraicSpace
