module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A depth improvement of `F` along `Z` is a module morphism that is unchanged off `Z`,
is surjective with depth-one target stalks on the boundary reached immediately from
`associatedPoints F`, and has target stalk depth at least two at the remaining points. -/
structure IsDepthImprovement {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    {F G : X.Modules} (φ : F ⟶ G) : Prop where
  isIso_stalk (x : X) (hx : x ∉ Z) :
    IsIso (RingedSpace.moduleStalkHom x φ)
  surjective_stalk_of_boundary (x : X) (hx : x ∈ Z)
      (hboundary : ∃ x' : X,
        IsImmediateSpecialization x' x ∧ x' ∉ Z ∧ x' ∈ F.associatedPoints) :
    Function.Surjective (RingedSpace.moduleStalkMap x φ)
  depth_eq_one_of_boundary (x : X) (hx : x ∈ Z)
      (hboundary : ∃ x' : X,
        IsImmediateSpecialization x' x ∧ x' ∉ Z ∧ x' ∈ F.associatedPoints) :
    moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x) = (1 : ℕ∞)
  depth_ge_two_of_not_boundary (x : X) (hx : x ∈ Z)
      (hboundary : ¬ ∃ x' : X,
        IsImmediateSpecialization x' x ∧ x' ∉ Z ∧ x' ∈ F.associatedPoints) :
    (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)

namespace IsDepthImprovement

/-- Construct a depth improvement from its four stalkwise conditions. -/
def ofConditions {X : Scheme.{u}} {Z : TopologicalSpace.Closeds X}
    {F G : X.Modules} {φ : F ⟶ G}
    (h_isIso : ∀ x : X, x ∉ Z → IsIso (RingedSpace.moduleStalkHom x φ))
    (h_surjective : ∀ x : X, x ∈ Z →
      (∃ x' : X, IsImmediateSpecialization x' x ∧ x' ∉ Z ∧
        x' ∈ F.associatedPoints) →
      Function.Surjective (RingedSpace.moduleStalkMap x φ))
    (h_depth_one : ∀ x : X, x ∈ Z →
      (∃ x' : X, IsImmediateSpecialization x' x ∧ x' ∉ Z ∧
        x' ∈ F.associatedPoints) →
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x) = (1 : ℕ∞))
    (h_depth_two : ∀ x : X, x ∈ Z →
      (¬ ∃ x' : X, IsImmediateSpecialization x' x ∧ x' ∉ Z ∧
        x' ∈ F.associatedPoints) →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) :
    IsDepthImprovement Z φ :=
  { isIso_stalk := h_isIso
    surjective_stalk_of_boundary := h_surjective
    depth_eq_one_of_boundary := h_depth_one
    depth_ge_two_of_not_boundary := h_depth_two }

/-- The stalk-map conditions supplied by a depth improvement. -/
theorem stalk_spec {X : Scheme.{u}} {Z : TopologicalSpace.Closeds X}
    {F G : X.Modules} {φ : F ⟶ G} (hφ : IsDepthImprovement Z φ) :
    (∀ x : X, x ∉ Z → IsIso (RingedSpace.moduleStalkHom x φ)) ∧
      ∀ x : X, x ∈ Z →
        (∃ x' : X, IsImmediateSpecialization x' x ∧ x' ∉ Z ∧
          x' ∈ F.associatedPoints) →
        Function.Surjective (RingedSpace.moduleStalkMap x φ) := sorry

/-- The two depth strata supplied by a depth improvement. -/
theorem depth_spec {X : Scheme.{u}} {Z : TopologicalSpace.Closeds X}
    {F G : X.Modules} {φ : F ⟶ G} (hφ : IsDepthImprovement Z φ) :
    (∀ x : X, x ∈ Z →
      (∃ x' : X, IsImmediateSpecialization x' x ∧ x' ∉ Z ∧
        x' ∈ F.associatedPoints) →
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x) = (1 : ℕ∞)) ∧
      ∀ x : X, x ∈ Z →
        (¬ ∃ x' : X, IsImmediateSpecialization x' x ∧ x' ∉ Z ∧
          x' ∈ F.associatedPoints) →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat G x) := sorry

/-- On a Noetherian universally catenary scheme with `(S₁)` formal fibers, a coherent module
has a coherent depth improvement along any closed subset, unique up to a unique target
isomorphism compatible with the source map. -/
theorem existsUniqueIso {X : Scheme.{u}}
    [IsNoetherian X] [UniversallyCatenary X]
    (Z : TopologicalSpace.Closeds X) (F : X.Modules) [F.IsCoherent]
    (h_formal : ∀ x : X,
      (FieldAlgebraProperty.serreConditionS 1).HoldsOnFormalFibers
        (X.presheaf.stalk x)) :
    ∃ (G : X.Modules) (hG : G.IsCoherent) (φ : F ⟶ G),
      IsDepthImprovement Z φ ∧
        ∀ (H : X.Modules) (hH : H.IsCoherent) (ψ : F ⟶ H),
          IsDepthImprovement Z ψ →
            ∃! e : G ≅ H, φ ≫ e.hom = ψ := sorry

/-- Cohen–Macaulay pullback preserves a depth improvement over the inverse-image closed
subset on Noetherian schemes. -/
theorem pullback_of_cohenMacaulay {X Y : Scheme.{u}}
    [IsNoetherian X] [UniversallyCatenary X] [IsNoetherian Y]
    (Z : TopologicalSpace.Closeds X) (F G : X.Modules)
    [F.IsCoherent] [G.IsCoherent] (φ : F ⟶ G)
    (hφ : IsDepthImprovement Z φ)
    (h_formal : ∀ x : X,
      (FieldAlgebraProperty.serreConditionS 1).HoldsOnFormalFibers
        (X.presheaf.stalk x))
    (f : Y ⟶ X) [AlgebraicGeometry.CohenMacaulay f] :
    IsDepthImprovement (Z.preimage f.continuous) ((pullback f).map φ) := sorry

end IsDepthImprovement

end AlgebraicGeometry.Scheme.Modules
