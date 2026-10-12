/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
import StacksCheckRecall

open CategoryTheory

open AlgebraicGeometry

universe u

variable {X X' S S' : Scheme.{u}}

/- Lemma 35.34.6 (1): a commutative square of scheme morphisms induces a pullback functor on
the corresponding singleton-family categories of descent data. -/
@[stacks 023Y] #check (AlgebraicGeometry.Scheme.DescentData.Pullback.functor :
  (a : X ⟶ S) → (a' : X' ⟶ S') → (h : S' ⟶ S) →
    (f : X' ⟶ X) → CommSq f a' a h →
      Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) ⥤
        Scheme.DescentData (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a'))

#check (Scheme.DescentData.Pullback.functor_obj_obj :
  (a : X ⟶ S) → (a' : X' ⟶ S') → (h : S' ⟶ S) →
    (f : X' ⟶ X) → (sq : CommSq f a' a h) →
      (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)) →
        ((Scheme.DescentData.Pullback.functor a a' h f sq).obj D).obj PUnit.unit =
          (Over.pullback f).obj (D.obj PUnit.unit))

#check (Scheme.DescentData.Pullback.functor_obj_hom :
  (a : X ⟶ S) → (a' : X' ⟶ S') → (h : S' ⟶ S) →
    (f : X' ⟶ X) → (sq : CommSq f a' a h) →
      (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)) →
        {Y : Scheme.{u}} → (q : Y ⟶ S') → (g₀ g₁ : Y ⟶ X') →
          (hg₀ : g₀ ≫ a' = q) → (hg₁ : g₁ ≫ a' = q) →
            ((Scheme.DescentData.Pullback.functor a a' h f sq).obj D).hom
                (i₁ := PUnit.unit) (i₂ := PUnit.unit) q g₀ g₁ hg₀ hg₁ =
              Scheme.DescentData.Pullback.transitionMap
                a a' h f sq D q g₀ g₁ hg₀ hg₁)

/- Lemma 35.34.6 (2): two choices of the top morphism in the commutative square induce
canonically naturally isomorphic pullback functors. -/
@[stacks 023Y] #check (AlgebraicGeometry.Scheme.DescentData.Pullback.iso :
  (a : X ⟶ S) → (a' : X' ⟶ S') → (h : S' ⟶ S) →
    (f₀ f₁ : X' ⟶ X) → (sq₀ : CommSq f₀ a' a h) → (sq₁ : CommSq f₁ a' a h) →
      Scheme.DescentData.Pullback.functor a a' h f₀ sq₀ ≅
        Scheme.DescentData.Pullback.functor a a' h f₁ sq₁)
