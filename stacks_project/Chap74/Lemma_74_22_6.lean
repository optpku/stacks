module

public import stacks_project.Chap74.Lemma_74_22_6_Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}

/- Lemma 74.22.6 (1): a commutative square of algebraic spaces over a scheme `S` induces a
pullback functor on the corresponding singleton-family categories of descent data. -/
@[stacks 0ADL] #check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f : Y' ⟶ Y) → CommSq f a' a h →
      AlgebraicGeometry.AlgebraicSpace.DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a) ⥤
        AlgebraicGeometry.AlgebraicSpace.DescentData (fun _ : PUnit.{v + 1} ↦ Y') (fun _ ↦ a'))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor_obj_obj :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f : Y' ⟶ Y) → (sq : CommSq f a' a h) →
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)) →
        ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f sq).obj D).obj
            PUnit.unit =
          (AlgebraicGeometry.AlgebraicSpace.overPullback f).obj (D.obj PUnit.unit))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor_obj_hom :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f : Y' ⟶ Y) → (sq : CommSq f a' a h) →
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)) →
        {Z : AlgebraicSpace S} → (q : Z ⟶ X') → (g₀ g₁ : Z ⟶ Y') →
          (hg₀ : g₀ ≫ a' = q) → (hg₁ : g₁ ≫ a' = q) →
            ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f sq).obj D).hom
                (i₁ := PUnit.unit) (i₂ := PUnit.unit) q g₀ g₁ hg₀ hg₁ =
              AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.transitionMap
                a a' h f sq D q g₀ g₁ hg₀ hg₁)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor_map_hom :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f : Y' ⟶ Y) → (sq : CommSq f a' a h) →
      {D E : AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)} →
        (φ : D ⟶ E) →
          ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f sq).map φ).hom
              PUnit.unit =
            (AlgebraicGeometry.AlgebraicSpace.overPullback f).map (φ.hom PUnit.unit))

/- Lemma 74.22.6 (2): two morphisms `f₀, f₁ : Y' ⟶ Y` completing the same commutative square
induce canonically isomorphic pullback functors on descent data. -/
@[stacks 0ADL] #check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.iso :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f₀ f₁ : Y' ⟶ Y) → (sq₀ : CommSq f₀ a' a h) → (sq₁ : CommSq f₁ a' a h) →
      AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f₀ sq₀ ≅
        AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f₁ sq₁)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.iso_hom_app_hom :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f₀ f₁ : Y' ⟶ Y) → (sq₀ : CommSq f₀ a' a h) → (sq₁ : CommSq f₁ a' a h) →
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)) →
        ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.iso a a' h f₀ f₁ sq₀ sq₁).hom.app
            D).hom PUnit.unit =
          (D.iso (a' ≫ h) f₀ f₁ sq₀.w sq₁.w).hom)
