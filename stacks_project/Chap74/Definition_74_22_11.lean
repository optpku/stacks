module

public import stacks_project.Chap74.Definition_74_22_11_Effectivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Definition 74.22.11 (1): Pulling back an algebraic space `U` over `X` along a
family `f i : Xᵢ i ⟶ X` gives the canonical descent datum `(Xᵢ ×_X U, can)`. -/
@[stacks 0ADR] #check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
      Over X → AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f)

#check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj_obj :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      (U : Over X) (i : I),
      (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj Xᵢ f U).obj i =
        (AlgebraicGeometry.AlgebraicSpace.overPullback (f i)).obj U)

#check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.trivial :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S},
      Over X →
        AlgebraicGeometry.AlgebraicSpace.DescentData
          (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X))

#check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.ofObjIsoPullbackTrivial :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      (U : Over X),
      AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj Xᵢ f U ≅
        (AlgebraicGeometry.AlgebraicSpace.DescentData.trivialPullback Xᵢ f).obj
          (AlgebraicGeometry.AlgebraicSpace.DescentData.trivial U))

/- Definition 74.22.11 (2): A descent datum relative to `{Xᵢ → X}` is effective
when it is isomorphic to a canonical datum `(Xᵢ ×_X U, can)`. -/
@[stacks 0ADR] #check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X},
      AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f → Prop)

#check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.isEffective_iff :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X}
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f),
      D.IsEffective ↔
        ∃ U : Over X,
          Nonempty (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj Xᵢ f U ≅ D))

#check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective.ofObj :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X}
      (U : Over X),
      AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective
        (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj Xᵢ f U))

#check
  (@AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective.ofIso :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X}
      {D E : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f},
      (D ≅ E) → AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective D →
      AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective E)
