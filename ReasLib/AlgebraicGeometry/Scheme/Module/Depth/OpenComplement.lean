module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Open

/-!
# Depth and extension across an open complement

This file relates depth conditions away from an open subset to extension of coherent scheme
modules and their global sections.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (U : X.Opens) (ℱ : X.Modules) [ℱ.IsCoherent]

/-- A coherent module whose stalks have depth at least two away from an open subset is
isomorphic to the pushforward of its restriction to that open subset. -/
theorem isIso_pullbackPushforward_unit_of_moduleDepth_ge_two_off_open
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app ℱ) := sorry

/-- Restriction of global sections of a coherent module is an isomorphism when its stalks have
depth at least two away from the open subset. -/
theorem isIso_globalSectionsRestrict_of_moduleDepth_ge_two_off_open
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) :
    IsIso (globalSectionsRestrict U ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
