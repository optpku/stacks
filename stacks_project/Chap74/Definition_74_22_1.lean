/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Slice
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Definition 74.22.1: the category of descent data relative to a morphism
`f : Y ⟶ X` of algebraic spaces over a scheme `S`. -/
@[stacks 0ADG] #check
  (CategoryTheory.Over.DescentData
      (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) :
    Type (max (max v (u + 1)) u))

variable
  (sq : ∀ i j : PUnit.{v + 1}, ChosenPullback f f)
  (sq₃ : ∀ i j k : PUnit.{v + 1}, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
  (V : ∀ i : PUnit.{v + 1}, Over Y)
  (φ : ∀ i j : PUnit.{v + 1},
    (CategoryTheory.Over.pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
      (CategoryTheory.Over.pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
  (hφ : ∀ i j k : PUnit.{v + 1},
    Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)

variable (D E : CategoryTheory.Over.DescentData.Chosen
    (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃)
variable (ψ : D ⟶ E)

#check (CategoryTheory.Over.DescentData.Chosen.ofIso
  (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃ V φ hφ :
  CategoryTheory.Over.DescentData.Chosen
    (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃)
#check (CategoryTheory.Over.DescentData.Chosen.iso
  (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃ D PUnit.unit PUnit.unit :
  (CategoryTheory.Over.pseudofunctor.map (sq PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.obj
      (D.obj PUnit.unit) ≅
    (CategoryTheory.Over.pseudofunctor.map (sq PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.obj
      (D.obj PUnit.unit))
#check (CategoryTheory.Over.DescentData.Chosen.cocycle
  (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃ D
    PUnit.unit PUnit.unit PUnit.unit)
#check (CategoryTheory.Over.DescentData.Chosen.hom_comm
  (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃ ψ PUnit.unit PUnit.unit)
#check (CategoryTheory.Over.DescentData.Chosen.equivalence
  (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃ :
  CategoryTheory.Over.DescentData.Chosen
      (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) sq sq₃ ≌
    CategoryTheory.Over.DescentData
      (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f))
