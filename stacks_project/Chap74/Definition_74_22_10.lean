module

public import stacks_project.Chap74.Definition_74_22_11_Effectivity
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/- Definition 74.22.10 (1): the trivial descent datum of an algebraic space `U`
over `X` relative to `𝟙 X` is the identity-family datum of `U`. -/
@[stacks 0ADQ] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.trivial :
    Over X →
      AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X))

variable (f : Y ⟶ X)

/- Definition 74.22.10 (2): pulling the trivial datum of `U` back along
`f : Y ⟶ X` yields the canonical descent datum `(Y ×_X U, can)`. -/
@[stacks 0ADQ] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj (fun _ : PUnit.{v + 1} ↦ Y)
    (fun _ ↦ f) :
      Over X →
        AlgebraicGeometry.AlgebraicSpace.DescentData
          (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj_obj
    (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) :
      ∀ (U : Over X) (i : PUnit.{v + 1}),
        (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj
            (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) U).obj i =
          (AlgebraicGeometry.AlgebraicSpace.overPullback f).obj U)

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObjIsoPullbackTrivial
    (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) :
      ∀ U : Over X,
        AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj
            (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) U ≅
          (AlgebraicGeometry.AlgebraicSpace.DescentData.trivialPullback
              (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f)).obj
            (AlgebraicGeometry.AlgebraicSpace.DescentData.trivial U))

/- Definition 74.22.10 (3): a descent datum relative to `Y / X` is effective
when it is isomorphic to the canonical datum `(Y ×_X U, can)` for some
algebraic space `U` over `X`. -/
@[stacks 0ADQ] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective :
    AlgebraicGeometry.AlgebraicSpace.DescentData
      (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.isEffective_iff :
    ∀ D : AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f),
      D.IsEffective ↔
        ∃ U : Over X, Nonempty
          (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj
              (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) U ≅ D))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective.ofObj :
    ∀ U : Over X,
      AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective
        (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj
          (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f) U))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective.ofIso :
    ∀ {D E : AlgebraicGeometry.AlgebraicSpace.DescentData
        (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ f)},
      (D ≅ E) → AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective D →
        AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective E)
