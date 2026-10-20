module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Stalk
public import ReasLib.RingTheory.Henselian.StrictHenselization.WeaklyEtale

@[expose] public section

/-!
# Weakly Étale Scheme Morphisms and Strict Henselizations
-/

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A scheme morphism is weakly étale exactly when every stalk map induces isomorphisms on
compatible strict henselizations. -/
@[stacks 094Z]
theorem iff_stalkMap_isIsoOnStrictHenselizations {X Y : Scheme.{u}} (f : X ⟶ Y) :
    WeaklyEtale f ↔
      ∀ x : X, (f.stalkMap x).hom.IsIsoOnStrictHenselizations := sorry

end AlgebraicGeometry.WeaklyEtale
