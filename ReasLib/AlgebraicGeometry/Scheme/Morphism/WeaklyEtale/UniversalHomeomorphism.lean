module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A weakly étale universal homeomorphism of schemes is an isomorphism. -/
instance (priority := 900) instIsIsoOfUniversalHomeomorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [WeaklyEtale f] [UniversalHomeomorphism f] : IsIso f := sorry

end AlgebraicGeometry.WeaklyEtale
