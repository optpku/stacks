module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_7_2_Pullback

/-!
# Fibre products in the category of algebraic spaces

If `F ⟶ H` and `G ⟶ H` are morphisms of algebraic spaces over a scheme `S`, then the sheaf
fibre product `F ×_H G` is the fibre product in `AlgebraicSpace S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The mediating morphism `W ⟶ F ×_H G` induced by a commutative cone `W ⟶ F`, `W ⟶ G`
over `H`. -/
def pullbackLift {S : Scheme.{u}} {W F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H)
    (h : W ⟶ F) (k : W ⟶ G) (w : h ≫ f = k ≫ g) :
    W ⟶ pullbackOver f g H.isSheaf H.representableDiagonal :=
  ReasLibPullback.pullbackLift f g h k w

/-- The mediating morphism `pullbackLift f g h k w` recovers the given map `h : W ⟶ F`. -/
theorem pullbackLift_fst {S : Scheme.{u}} {W F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H)
    (h : W ⟶ F) (k : W ⟶ G) (w : h ≫ f = k ≫ g) :
    pullbackLift f g h k w ≫ pullbackOverFst f g H.isSheaf H.representableDiagonal = h :=
  ReasLibPullback.pullbackLift_fst f g h k w

/-- The mediating morphism `pullbackLift f g h k w` recovers the given map `k : W ⟶ G`. -/
theorem pullbackLift_snd {S : Scheme.{u}} {W F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H)
    (h : W ⟶ F) (k : W ⟶ G) (w : h ≫ f = k ≫ g) :
    pullbackLift f g h k w ≫ pullbackOverSnd f g H.isSheaf H.representableDiagonal = k :=
  ReasLibPullback.pullbackLift_snd f g h k w

/-- The projections of `F ×_H G` exhibit it as a fibre product of `f` and `g` in the category
of algebraic spaces over `S`. -/
theorem isPullback {S : Scheme.{u}} {F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback (pullbackOverFst f g H.isSheaf H.representableDiagonal)
      (pullbackOverSnd f g H.isSheaf H.representableDiagonal) f g :=
  ReasLibPullback.isPullback f g

/-- Morphisms of algebraic spaces over `S` admit fibre products. -/
instance hasPullback {S : Scheme.{u}} {F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H) :
    HasPullback f g :=
  ReasLibPullback.hasPullback f g

/-- The category of algebraic spaces over a scheme `S` has fibre products. -/
instance instHasPullbacks {S : Scheme.{u}} : HasPullbacks (AlgebraicSpace S) :=
  ReasLibPullback.instHasPullbacks

end AlgebraicGeometry.AlgebraicSpace
