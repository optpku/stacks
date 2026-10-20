module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection

@[expose] public section

universe u

#check (AlgebraicGeometry.LocallyOfType.instHasRingHomPropertyIsLocalCompleteIntersection :
  AlgebraicGeometry.HasRingHomProperty
    (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection)
    RingHom.IsLocalCompleteIntersection)
