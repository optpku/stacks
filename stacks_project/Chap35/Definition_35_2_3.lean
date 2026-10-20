module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Canonical
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Definition 35.2.3 (1): The trivial descent datum of a quasi-coherent
`𝒪_S`-module is its canonical datum for the singleton identity family. -/
@[stacks 023D]
#check (@AlgebraicGeometry.Scheme.QCoh.DescentData.trivial :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.Scheme.QCoh S →
    AlgebraicGeometry.Scheme.QCoh.DescentData (fun _ : Unit ↦ S) (fun _ ↦ 𝟙 S))

/- Definition 35.2.3 (2): The canonical descent datum `(𝓕|_{Sᵢ}, can)` is the
pullback of the trivial descent datum along a family of scheme morphisms. -/
@[stacks 023D]
#check (@AlgebraicGeometry.Scheme.QCoh.DescentData.canonical :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S),
    AlgebraicGeometry.Scheme.QCoh S → AlgebraicGeometry.Scheme.QCoh.DescentData X f)

/- Definition 35.2.3 (3): A quasi-coherent descent datum is effective when it is
isomorphic to the canonical datum of a quasi-coherent module on the base scheme. -/
@[stacks 023D]
#check (@AlgebraicGeometry.Scheme.QCoh.DescentData.IsEffective :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S},
    AlgebraicGeometry.Scheme.QCoh.DescentData X f → Prop)
