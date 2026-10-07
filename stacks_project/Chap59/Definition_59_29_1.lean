module

public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Definition 59.29.1 (1): A geometric point of a scheme is a morphism from the spectrum of an
algebraically closed field. -/
@[stacks 03PO] #check (AlgebraicGeometry.Scheme.GeometricPoint : Scheme.{u} → Type (u + 1))

/- Definition 59.29.1 (2): An étale neighborhood of a geometric point is an étale scheme over the
base scheme together with a chosen lift of the geometric point. -/
@[stacks 03PO] #check (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood :
  {S : Scheme.{u}} → GeometricPoint S → Type (u + 1))

/- Definition 59.29.1 (3): A morphism of étale neighborhoods is an `S`-morphism preserving the
chosen lifts. -/
@[stacks 03PO] #check (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.Hom :
  {S : Scheme.{u}} → {s : GeometricPoint S} →
    GeometricPoint.EtaleNeighborhood s → GeometricPoint.EtaleNeighborhood s → Type u)
