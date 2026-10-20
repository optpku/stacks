module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Étale locality of perfect scheme morphisms

Perfectness of scheme morphisms is étale local on source-and-target.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Perfectness of scheme morphisms is étale local on source-and-target. -/
instance isPerfectRingMap_isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) :=
  sorry

end AlgebraicGeometry.LocallyOfType
