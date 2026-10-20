module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
  (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/- Definition 74.3.1: descent data for quasi-coherent sheaves with respect to a family of
morphisms of algebraic spaces over a scheme `S` with fixed target, together with their
compatible componentwise morphisms. -/
@[stacks 04W3] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Xᵢ f : Type (max (u + 1) v))

#check AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.ofIso
#check AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.homMk
#check AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.equivalence
