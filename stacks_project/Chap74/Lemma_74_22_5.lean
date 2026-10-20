/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Coproduct
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 74.22.5: for a scheme `S` and a small family `f i : Xᵢ i ⟶ X` of morphisms of
algebraic spaces over `S`, descent data relative to the family are canonically equivalent to
descent data relative to `Y ⟶ X` with `Y = coproduct Xᵢ`, via `V = coproduct` of the component
spaces `Vᵢ` and `φ = coproduct` of the pairwise comparisons `φᵢⱼ`. -/
@[stacks 0ADK] #check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence :
    ∀ {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : AlgebraicSpace S}
      (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
      AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f ≌
        AlgebraicGeometry.AlgebraicSpace.DescentData
          (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductFamily Xᵢ)
          (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductArrow Xᵢ f))

open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.DescentData

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.assembleCoproduct Xᵢ f :
    DescentData Xᵢ f ⥤ DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.restrictCoproduct Xᵢ f :
    DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f) ⥤ DescentData Xᵢ f)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence_obj Xᵢ f :
    ∀ (D : DescentData Xᵢ f) (p : PUnit.{v + 1}),
    ((coproductEquivalence Xᵢ f).functor.obj D).obj p =
      Over.mk (coproductDesc fun i ↦ (D.obj i).hom ≫ coproductι Xᵢ i))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence_hom_ι Xᵢ f :
    ∀ (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j k : I),
    assembledHomLocalToW Xᵢ f D a b j k ≫
        assembledHomSourceι Xᵢ f D a j ≫
          ((((coproductEquivalence Xᵢ f).functor.obj D).hom
            (i₁ := PUnit.unit) (i₂ := PUnit.unit) q a b ha hb).left) =
      assembledHomLocalLift Xᵢ f D q a b ha hb j k)
