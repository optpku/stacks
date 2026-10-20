module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.OpenComplement
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

universe u

/- Lemma 31.5.11: let `X` be a locally Noetherian scheme, let `ℱ` be a coherent
`𝒪_X`-module, and let `U` be an open subscheme of `X`. If every point outside `U` has stalk
depth at least two, then `ℱ ⟶ U.ι_* (ℱ|_U)` is an isomorphism. -/
@[stacks 0E9I] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_pullbackPushforward_unit_of_moduleDepth_ge_two_off_open :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (ℱ : X.Modules) [ℱ.IsCoherent],
      (∀ x : X, x ∉ U →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) →
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app ℱ))

#check
  (AlgebraicGeometry.Scheme.Modules.isIso_globalSectionsRestrict_of_moduleDepth_ge_two_off_open :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (ℱ : X.Modules) [ℱ.IsCoherent],
      (∀ x : X, x ∉ U →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) →
      IsIso (Scheme.Modules.globalSectionsRestrict U ℱ))
