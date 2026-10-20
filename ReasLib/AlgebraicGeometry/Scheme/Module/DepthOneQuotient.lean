module

public import Mathlib.Topology.Inseparable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.RingTheory.Depth

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quotient of a scheme module with unchanged stalks off `T` and stalk depth at least one
on `T`. -/
structure IsDepthOneQuotient {X : Scheme.{u}} (T : Set X)
    {F G : X.Modules} (π : F ⟶ G) : Prop where
  epi : Epi π
  isIso_stalk (x : X) (hx : x ∉ T) :
    IsIso (RingedSpace.moduleStalkHom x π)
  depth_ge_one (x : X) (hx : x ∈ T) :
    (1 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)

namespace IsDepthOneQuotient

/-- Epicness, stalk isomorphisms off a subset, and target-stalk depth at least one on that
subset imply the depth-one quotient property. -/
def ofConditions {X : Scheme.{u}} {T : Set X} {F G : X.Modules} {π : F ⟶ G}
    (h_epi : Epi π)
    (h_isIso : ∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x π))
    (h_depth : ∀ x : X, x ∈ T →
      (1 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)) :
    IsDepthOneQuotient T π :=
  ⟨h_epi, h_isIso, h_depth⟩

end IsDepthOneQuotient

/-- A morphism is a depth-one quotient exactly when it is epic, unchanged on stalks off the
specified subset, and its target stalks have depth at least one on that subset. -/
theorem isDepthOneQuotient_iff {X : Scheme.{u}} (T : Set X)
    {F G : X.Modules} (π : F ⟶ G) :
    IsDepthOneQuotient T π ↔
      Epi π ∧
        (∀ x : X, x ∉ T → IsIso (RingedSpace.moduleStalkHom x π)) ∧
          ∀ x : X, x ∈ T →
            (1 : ℕ∞) ≤
              moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x) := sorry

namespace IsDepthOneQuotient

/-- A coherent module on a Noetherian scheme has a coherent depth-one quotient along any
subset stable under specialization. -/
theorem «exists» {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (_ : G.IsCoherent) (π : F ⟶ G),
      IsDepthOneQuotient T π := sorry

/-- Two coherent depth-one quotients along a specialization-stable subset of a Noetherian
scheme are related by a unique target isomorphism compatible with their source maps. -/
theorem existsUniqueIso {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F G H : X.Modules) [F.IsCoherent] [G.IsCoherent] [H.IsCoherent]
    (π : F ⟶ G) (ρ : F ⟶ H)
    (hπ : IsDepthOneQuotient T π) (hρ : IsDepthOneQuotient T ρ) :
    ∃! e : G ≅ H, π ≫ e.hom = ρ := sorry

/-- Flat pullback between Noetherian schemes preserves the depth-one quotient property for
coherent modules over the inverse image of the specialization-stable subset. -/
theorem pullback_of_flat {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (π : F ⟶ G) (hπ : IsDepthOneQuotient T π)
    (f : Y ⟶ X) [Flat f] :
    IsDepthOneQuotient (f.base ⁻¹' T) ((pullback f).map π) := sorry

end IsDepthOneQuotient

end AlgebraicGeometry.Scheme.Modules
