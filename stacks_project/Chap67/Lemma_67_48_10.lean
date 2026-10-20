module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Integral
import StacksCheckRecall

/-!
# Integral morphisms of algebraic spaces are their own relative normalization

If `f : X ⟶ Y` is an integral morphism of algebraic spaces, then the canonical
map `toNormalization f : X ⟶ Hom.normalization f` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.48.10: let `S` be a scheme. Let `f : X ⟶ Y` be an integral morphism
of algebraic spaces over `S`. Then the integral closure of `Y` in `X` is equal
to `X`. -/
@[stacks 0825]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.isNormalization_id_of_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f],
      IsNormalization f (𝟙 X) f)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.instIsIso_toNormalization_of_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom f],
      IsIso (Hom.toNormalization f))
