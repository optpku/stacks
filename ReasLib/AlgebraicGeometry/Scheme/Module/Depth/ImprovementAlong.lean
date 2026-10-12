/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Inseparable
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.DepthOneQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.ExtensionAlong
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A module morphism improves depth along `T' ⊆ T` when it is an isomorphism off `T`,
surjective with depth at least one on `T \ T'`, and has depth at least two on `T'`. -/
structure IsDepthImprovementAlong {X : Scheme.{u}} (T' T : Set X)
    {F G : X.Modules} (φ : F ⟶ G) : Prop where
  isIso_stalk (x : X) (hx : x ∉ T) :
    IsIso (RingedSpace.moduleStalkHom x φ)
  surjective_stalk (x : X) (hxT : x ∈ T) (hxT' : x ∉ T') :
    Function.Surjective (RingedSpace.moduleStalkMap x φ)
  depth_ge_one (x : X) (hxT : x ∈ T) (hxT' : x ∉ T') :
    (1 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)
  depth_ge_two (x : X) (hxT' : x ∈ T') :
    (2 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)

namespace IsDepthImprovementAlong

/-- A stalkwise isomorphism off `T`, surjectivity and depth at least one on `T \ T'`,
and depth at least two on `T'` determine a depth improvement along `T' ⊆ T`. -/
def fromConditions {X : Scheme.{u}} {T' T : Set X}
    {F G : X.Modules} {φ : F ⟶ G}
    (h_isIso : ∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ))
    (h_surjective : ∀ x : X, x ∈ T → x ∉ T' →
      Function.Surjective (RingedSpace.moduleStalkMap x φ))
    (h_depth_one : ∀ x : X, x ∈ T → x ∉ T' →
      (1 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x))
    (h_depth_two : ∀ x : X, x ∈ T' →
      (2 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) :
    IsDepthImprovementAlong T' T φ :=
  { isIso_stalk := h_isIso
    surjective_stalk := h_surjective
    depth_ge_one := h_depth_one
    depth_ge_two := h_depth_two }

/-- Construct the depth-improvement property from its four stalkwise conditions. -/
theorem ofConditions {X : Scheme.{u}} {T' T : Set X}
    {F G : X.Modules} {φ : F ⟶ G}
    (h_isIso : ∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ))
    (h_surjective : ∀ x : X, x ∈ T → x ∉ T' →
      Function.Surjective (RingedSpace.moduleStalkMap x φ))
    (h_depth_one : ∀ x : X, x ∈ T → x ∉ T' →
      (1 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x))
    (h_depth_two : ∀ x : X, x ∈ T' →
      (2 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) :
    IsDepthImprovementAlong T' T φ := sorry

/-- The stalk-isomorphism and stalk-surjectivity clauses supplied by a depth improvement. -/
theorem stalk_spec {X : Scheme.{u}} {T' T : Set X}
    {F G : X.Modules} {φ : F ⟶ G} (hφ : IsDepthImprovementAlong T' T φ) :
    (∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ)) ∧
      ∀ x : X, x ∈ T → x ∉ T' →
        Function.Surjective (RingedSpace.moduleStalkMap x φ) := sorry

/-- The depth-one and depth-two strata supplied by a depth improvement. -/
theorem depth_spec {X : Scheme.{u}} {T' T : Set X}
    {F G : X.Modules} {φ : F ⟶ G} (hφ : IsDepthImprovementAlong T' T φ) :
    (∀ x : X, x ∈ T → x ∉ T' →
      (1 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) ∧
      ∀ x : X, x ∈ T' →
        (2 : ℕ∞) ≤
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x) := sorry

end IsDepthImprovementAlong

/-- The depth-improvement property is equivalent to its four stalkwise conditions, grouped by
stalk maps and depth strata. -/
theorem isDepthImprovementAlong_iff {X : Scheme.{u}} (T' T : Set X)
    {F G : X.Modules} (φ : F ⟶ G) :
    IsDepthImprovementAlong T' T φ ↔
      ((∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x φ)) ∧
        (∀ x : X, x ∈ T → x ∉ T' →
          Function.Surjective (RingedSpace.moduleStalkMap x φ))) ∧
      ((∀ x : X, x ∈ T → x ∉ T' →
          (1 : ℕ∞) ≤
            moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x))) ∧
        (∀ x : X, x ∈ T' →
          (2 : ℕ∞) ≤
            moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) := sorry

namespace IsDepthImprovementAlong

/-- A coherent module on a Noetherian scheme locally admitting dualizing complexes has a unique
coherent depth improvement along two specialization-stable subsets. -/
theorem existsUniqueIso {X : Scheme.{u}} [IsNoetherian X]
    (T' T : Set X)
    (hT' : StableUnderSpecialization T')
    (hT : StableUnderSpecialization T)
    (hTT' : T' ⊆ T)
    (h_immediate : ∀ ⦃x x' : X⦄,
      IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (hdual : LocallyHasDualizingComplex X)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (hG : G.IsCoherent) (φ : F ⟶ G),
      IsDepthImprovementAlong T' T φ ∧
        ∀ (H : X.Modules) (hH : H.IsCoherent) (ψ : F ⟶ H),
          IsDepthImprovementAlong T' T ψ →
            ∃! e : G ≅ H, φ ≫ e.hom = ψ := sorry

/-- A Cohen–Macaulay pullback preserves depth improvement along inverse-image subsets. -/
theorem pullback_of_cohenMacaulay {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (T' T : Set X)
    (hT' : StableUnderSpecialization T')
    (hT : StableUnderSpecialization T)
    (hTT' : T' ⊆ T)
    (h_immediate : ∀ ⦃x x' : X⦄,
      IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (φ : F ⟶ G) (hφ : IsDepthImprovementAlong T' T φ)
    (f : Y ⟶ X) [AlgebraicGeometry.CohenMacaulay f] :
    IsDepthImprovementAlong (f.base ⁻¹' T') (f.base ⁻¹' T) ((pullback f).map φ) := sorry

end IsDepthImprovementAlong

end AlgebraicGeometry.Scheme.Modules
