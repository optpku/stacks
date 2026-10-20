module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.VectorFields

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.SchemeOverField
open SheafOfModules
open PresheafOfModules.Derivation'

universe u

/- The fixed-point predicate for a structure-sheaf derivation is available to chapter consumers. -/
#check (AlgebraicGeometry.Curve.derivationFixesAt :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
      derivations X.hom.toShHom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) →
      closedPoints X.left → Prop)

/- The sectionwise zero predicate for a structure-sheaf derivation is available to chapter consumers. -/
#check (AlgebraicGeometry.Curve.derivationIsZero :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
      derivations X.hom.toShHom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) → Prop)
