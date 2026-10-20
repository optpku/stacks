module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ClosedImmersion.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact

@[expose] public section

/-!
# Derived adjunction for closed immersions

The derived pushforward along a closed immersion is left adjoint to the derived internal Hom
from the source structure sheaf.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

/-- Derived pushforward along a closed immersion is left adjoint to the derived internal Hom from
the source structure sheaf. -/
@[stacks 0A76]
noncomputable def adjunction
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    RingedSpace.moduleDerivedPushforward i ⊣
      rHomFromStructureSheaf i h_closed := by
  -- Local instance justification (proof-local temporary data): underived right-adjoint additivity is needed only while constructing this derived adjunction.
  letI : (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
      i h_closed).Additive :=
    (RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction
      i h_closed).right_adjoint_additive
  let pushforwardExact : Z.Modules ⥤ₑ X.Modules :=
    ⟨RingedSpace.Hom.pushforward i,
      RingedSpace.Hom.ModulePushforward.ClosedImmersion.exact i h_closed⟩
  -- Local instance justification (proof-local temporary data): expose finite-limit preservation only for the homotopy comparison construction.
  letI : PreservesFiniteLimits pushforwardExact.obj := pushforwardExact.property.1
  -- Local instance justification (proof-local temporary data): expose finite-colimit preservation only for the homotopy comparison construction.
  letI : PreservesFiniteColimits pushforwardExact.obj := pushforwardExact.property.2
  exact
    (Adjunction.Derived.KInjective.adjunction
      pushforwardExact
      (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
        i h_closed)
      (RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction i h_closed)).ofNatIsoLeft
      (Functor.RightDerived.Exact.homotopyIso pushforwardExact.obj)

end AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion

end
