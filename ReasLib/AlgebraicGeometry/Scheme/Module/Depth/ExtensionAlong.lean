/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Inseparable
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.LocalExistence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A module morphism is a depth-two extension along `T` when it is an isomorphism
on stalks off `T` and its target stalks have depth at least two on `T`. -/
structure IsDepthTwoExtensionAlong {X : Scheme.{u}} (T : Set X)
    {F G : X.Modules} (φ : F ⟶ G) : Prop where
  isIso_stalk (x : X) (hx : x ∉ T) :
    IsIso (RingedSpace.moduleStalkHom x φ)
  depth_ge_two (x : X) (hx : x ∈ T) :
    (2 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)

namespace IsDepthTwoExtensionAlong

/-- Construct the depth-two extension property from its stalkwise conditions. -/
def ofConditions {X : Scheme.{u}} {T : Set X} {F G : X.Modules} {φ : F ⟶ G}
    (h_isIso : ∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ))
    (h_depth : ∀ x : X, x ∈ T →
      (2 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) :
    IsDepthTwoExtensionAlong T φ := sorry

end IsDepthTwoExtensionAlong

/-- The defining stalkwise characterization of a depth-two extension along `T`. -/
theorem isDepthTwoExtensionAlong_iff {X : Scheme.{u}} (T : Set X)
    {F G : X.Modules} (φ : F ⟶ G) :
    IsDepthTwoExtensionAlong T φ ↔
      (∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ)) ∧
        ∀ x : X, x ∈ T →
          (2 : ℕ∞) ≤
            moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x) := sorry

namespace IsDepthTwoExtensionAlong

/-- A coherent module on a Noetherian scheme locally admitting dualizing complexes has a
coherent depth-two extension along a specialization-stable subset when its stalks have depth
at least one at immediate specializations entering that subset. -/
theorem «exists» {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (hdual : LocallyHasDualizingComplex X)
    (F : X.Modules) [F.IsCoherent]
    (hdepth : ∀ ⦃x x' : X⦄, IsImmediateSpecialization x x' →
      x' ∈ T → x ∉ T →
        (1 : ℕ∞) ≤
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)) :
    ∃ (G : X.Modules) (hG : G.IsCoherent) (φ : F ⟶ G),
      IsDepthTwoExtensionAlong T φ := sorry

/-- Two coherent depth-two extensions of a coherent module along a specialization-stable
subset of a Noetherian scheme locally admitting dualizing complexes are related by a unique
compatible target isomorphism under the immediate-specialization depth-one condition. -/
theorem existsUniqueIso {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (hdual : LocallyHasDualizingComplex X)
    (F G H : X.Modules) [F.IsCoherent] [G.IsCoherent] [H.IsCoherent]
    (hdepth : ∀ ⦃x x' : X⦄, IsImmediateSpecialization x x' →
      x' ∈ T → x ∉ T →
        (1 : ℕ∞) ≤
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x))
    (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : IsDepthTwoExtensionAlong T φ)
    (hψ : IsDepthTwoExtensionAlong T ψ) :
    ∃! e : G ≅ H, φ ≫ e.hom = ψ := sorry

/-- Cohen–Macaulay pullback between Noetherian schemes preserves coherent depth-two
extensions along the inverse image of a specialization-stable subset. -/
theorem pullback_of_cohenMacaulay {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (φ : F ⟶ G) (hφ : IsDepthTwoExtensionAlong T φ)
    (f : Y ⟶ X) [AlgebraicGeometry.CohenMacaulay f] :
    IsDepthTwoExtensionAlong (f.base ⁻¹' T) ((pullback f).map φ) := sorry

end IsDepthTwoExtensionAlong

end AlgebraicGeometry.Scheme.Modules
