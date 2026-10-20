module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Locality

/-!
# Stalkwise characterization of weakly étale scheme morphisms
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A scheme morphism is weakly étale if and only if each of its maps on local rings is
weakly étale. -/
theorem iff_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    WeaklyEtale f ↔ ∀ x : X, RingHom.WeaklyEtale (f.stalkMap x).hom := sorry

end AlgebraicGeometry.WeaklyEtale
