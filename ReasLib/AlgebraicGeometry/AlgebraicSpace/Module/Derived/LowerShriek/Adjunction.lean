module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.LowerShriek
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction

/-! # Derived étale lower-shriek adjunction -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- The derived adjunction `j_! ⊣ j^*` induced by étale extension by zero of
modules on algebraic spaces. -/
def lowerShriekDerivedAdjunction (f : U ⟶ X) [Etale f] :
    lowerShriekDerived f ⊣ restrictFunctorDerived f :=
  Adjunction.mapDerivedCategory (lowerShriekAdjunction f)

namespace lowerShriekDerived

/-- Derived étale lower shriek is a left adjoint. -/
instance instIsLeftAdjoint (f : U ⟶ X) [Etale f] :
    (lowerShriekDerived f).IsLeftAdjoint :=
  (lowerShriekDerivedAdjunction f).isLeftAdjoint

end lowerShriekDerived

namespace restrictFunctorDerived

/-- Derived étale restriction is a right adjoint. -/
instance instIsRightAdjoint (f : U ⟶ X) [Etale f] :
    (restrictFunctorDerived f).IsRightAdjoint :=
  (lowerShriekDerivedAdjunction f).isRightAdjoint

end restrictFunctorDerived

end AlgebraicGeometry.AlgebraicSpace.Modules
