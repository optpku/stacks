/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.ExtensionAlong

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Typed compatibility check for depth-two extensions along a subset. -/
#check (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtensionAlong :
  {X : Scheme.{u}} → (T : Set X) → {F G : X.Modules} → (F ⟶ G) → Prop)

/- Typed compatibility check for the stalkwise constructor. -/
#check (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtensionAlong.ofConditions :
  ∀ {X : Scheme.{u}} {T : Set X} {F G : X.Modules} {φ : F ⟶ G}
    (h_isIso : ∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ))
    (h_depth : ∀ x : X, x ∈ T →
      (2 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)),
    IsDepthTwoExtensionAlong T φ)

/- Typed compatibility check for the defining stalkwise characterization. -/
#check (AlgebraicGeometry.Scheme.Modules.isDepthTwoExtensionAlong_iff :
  ∀ {X : Scheme.{u}} (T : Set X) {F G : X.Modules} (φ : F ⟶ G),
    IsDepthTwoExtensionAlong T φ ↔
      (∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ)) ∧
        ∀ x : X, x ∈ T →
          (2 : ℕ∞) ≤
            moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x))

end AlgebraicGeometry.Scheme.Modules
