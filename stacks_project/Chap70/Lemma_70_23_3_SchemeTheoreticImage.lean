module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.SchemeTheoreticImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.baseChangeCone :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) {i : I}
    {X : AlgebraicSpace S} {f : X ⟶ c.pt}
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i)),
    Cone (baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi))
