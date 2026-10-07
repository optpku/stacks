module

public import stacks_project.Chap74.Definition_74_3_3_Canonical
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Definition 74.3.3 (1): The trivial descent datum of a quasi-coherent
`𝒪_X`-module is its canonical datum for the singleton identity family. -/
@[stacks 04W5]
#check (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.trivial :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.QCoh X →
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData (fun _ : Unit ↦ X) (fun _ ↦ 𝟙 X))

/- Definition 74.3.3 (2): The canonical descent datum `(F|_{Xᵢ}, can)` is the
pullback of the trivial descent datum along a family of morphisms of algebraic spaces. -/
@[stacks 04W5]
#check (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.canonical :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
    AlgebraicGeometry.AlgebraicSpace.QCoh X →
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Xᵢ f)

/- Definition 74.3.3 (3): A quasi-coherent descent datum is effective when it is
isomorphic to the canonical datum of a quasi-coherent module on the target algebraic space. -/
@[stacks 04W5]
#check (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.IsEffective :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X},
    AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Xᵢ f → Prop)
