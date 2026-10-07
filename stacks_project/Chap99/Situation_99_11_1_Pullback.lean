module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap99.Situation_99_11_1_PicardGroup

/-!
# Pullback on Picard groups of algebraic spaces

A morphism of algebraic spaces induces a contravariant additive map of Picard
groups by pulling back a chosen invertible representative and taking its class.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Modules

/-- Pullback of modules along a morphism of algebraic spaces preserves
tensor-invertibility. -/
instance pullback_isInvertibleObject {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : Y.Modules) [isInvertibleObject L] :
    isInvertibleObject ((pullback f).obj L) := sorry

end Modules

/-- The additive homomorphism `Pic(Y) →+ Pic(X)` induced by pullback along a
morphism of algebraic spaces. -/
def picardPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.PicardGroup →+ X.PicardGroup where
  toFun x := Modules.picardClass ((Modules.pullback f).obj (PicardGroup.repr x))
  map_zero' := sorry
  map_add' := sorry

/-- Pullback sends the class of an invertible module to the class of its
pullback. -/
theorem picardPullback_apply_class {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : Y.Modules) [isInvertibleObject L] :
    picardPullback f (Modules.picardClass L) =
      Modules.picardClass ((Modules.pullback f).obj L) := sorry

/-- Pullback along the identity morphism acts as the identity on the Picard
group. -/
theorem picardPullback_id {X : AlgebraicSpace S} :
    picardPullback (𝟙 X) = AddMonoidHom.id X.PicardGroup := sorry

/-- Pullback on Picard groups is contravariantly compatible with composition. -/
theorem picardPullback_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    picardPullback (f ≫ g) = (picardPullback f).comp (picardPullback g) := sorry

end AlgebraicGeometry.AlgebraicSpace
