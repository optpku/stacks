/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_22_8_Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v w

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S}
variable {I : Type v} {I' : Type w}
variable {Xᵢ : I → AlgebraicSpace S} {X'ᵢ : I' → AlgebraicSpace S}
variable {f : ∀ i, Xᵢ i ⟶ X} {f' : ∀ i, X'ᵢ i ⟶ X'}
variable {g : X' ⟶ X}

/- Lemma 74.22.8 (1): a morphism of fixed-target families pulls a descent datum back
componentwise along the maps `gᵢ`, with transition maps `(gᵢ × gⱼ)* φ`. -/
@[stacks 0ADN] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom_obj_obj :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f) → (i : I') →
          ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom
              α gᵢ comm).obj D).obj i =
            (AlgebraicGeometry.AlgebraicSpace.overPullback (gᵢ i)).obj (D.obj (α i)))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom_obj_hom :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f) →
          {Z : AlgebraicSpace S} → (q : Z ⟶ X') → {i j : I'} →
            (h₀ : Z ⟶ X'ᵢ i) → (h₁ : Z ⟶ X'ᵢ j) →
              (hh₀ : h₀ ≫ f' i = q) → (hh₁ : h₁ ≫ f' j = q) →
                ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom
                    α gᵢ comm).obj D).hom q h₀ h₁ hh₀ hh₁ =
                  Pseudofunctor.DescentData.pullFunctorObjHom
                    (F := AlgebraicGeometry.AlgebraicSpace.overPseudofunctor S)
                    (f := f) (p := g) (f' := f') (α := α) (p' := gᵢ) (w := comm)
                    D q h₀ h₁ hh₀ hh₁)

/- Lemma 74.22.8 (2): componentwise pullback defines a functor between the categories of
descent data relative to the two families. -/
@[stacks 0ADN] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f ⥤
          AlgebraicGeometry.AlgebraicSpace.DescentData X'ᵢ f')

/- Lemma 74.22.8 (3): two morphisms of families over the same base map induce canonically
isomorphic pullback functors on descent data. -/
@[stacks 0ADN] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.isoOfHom :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        (β : I' → I) → (hᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (β i)) →
          (comm' : ∀ i, hᵢ i ≫ f (β i) = f' i ≫ g) →
            AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom α gᵢ comm ≅
              AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom β hᵢ comm')

variable {I I' : Type v} [Small.{u} I] [Small.{u} I']
variable {Xᵢ : I → AlgebraicSpace S} {X'ᵢ : I' → AlgebraicSpace S}
variable {f : ∀ i, Xᵢ i ⟶ X} {f' : ∀ i, X'ᵢ i ⟶ X'}
variable (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
variable (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)

/- Lemma 74.22.8 (4): via the coproduct equivalences, family pullback agrees with
singleton-family pullback along the induced map of coproducts. -/
@[stacks 0ADN] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.coproductIsoOfHom α gᵢ comm :
    (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence Xᵢ f).functor ⋙
        AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor
          (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductArrow Xᵢ f PUnit.unit)
          (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductArrow X'ᵢ f' PUnit.unit) g
          (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.coproductMapOfHom α gᵢ)
          (CommSq.mk
            (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.coproductMapOfHom_fac
              α gᵢ comm)) ≅
      AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom α gᵢ comm ⋙
        (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence X'ᵢ f').functor)
