module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.BaseChange

/-!
# Depth-two extensions across open immersions

This file defines depth-two extensions of coherent scheme modules and records their canonical
extension, uniqueness, and flat-pullback properties.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of coherent modules is a depth-two extension across an open immersion when its
pullback is an isomorphism and its target has stalk depth at least two off the open image. -/
def IsDepthTwoExtension {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] (φ : F ⟶ G) : Prop :=
  IsIso ((pullback j).map φ) ∧
    ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat G x)

namespace IsDepthTwoExtension

/-- The adjunction unit from a coherent module to the pushforward of its restriction is a
depth-two extension when that pushforward is coherent. -/
theorem unit {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsCoherent]
    [((pushforward j).obj ((pullback j).obj F)).IsCoherent] :
    IsDepthTwoExtension j F ((pushforward j).obj ((pullback j).obj F))
      ((pullbackPushforwardAdjunction j).unit.app F) := sorry

/-- A depth-two extension morphism into the coherent pushforward of a restriction equals the
adjunction unit. -/
theorem unit_unique {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsCoherent]
    [((pushforward j).obj ((pullback j).obj F)).IsCoherent]
    (φ : F ⟶ (pushforward j).obj ((pullback j).obj F))
    (hφ : IsDepthTwoExtension j F ((pushforward j).obj ((pullback j).obj F)) φ) :
    φ = (pullbackPushforwardAdjunction j).unit.app F := sorry

/-- Flat pullback carries the canonical depth-two extension to the corresponding extension across
the inverse-image open immersion. -/
theorem pullbackUnit_of_flat {X U Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian Y]
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsCoherent]
    [((pushforward j).obj ((pullback j).obj F)).IsCoherent]
    (f : Y ⟶ X) [Flat f] :
    IsDepthTwoExtension (Limits.pullback.fst f j)
      ((pullback f).obj F)
      ((pullback f).obj ((pushforward j).obj ((pullback j).obj F)))
      ((pullback f).map ((pullbackPushforwardAdjunction j).unit.app F)) := sorry

end IsDepthTwoExtension

end AlgebraicGeometry.Scheme.Modules
