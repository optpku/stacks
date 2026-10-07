module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap76.Lemma_76_20_1_InfinitesimalLifting

/-!
# Infinitesimal lifting criterion for smoothness of algebraic spaces

For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, smoothness is equivalent to the infinitesimal lifting property against
small extensions of Artinian local rings whose bottom arrow is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The infinitesimal lifting property of `f` against small extensions of
Artinian local rings whose bottom arrow is of finite type. -/
def HasFiniteTypeSmallExtensionLifting {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] (π : B' →+* B) [π.IsSmallExtension]
    (σ : Spec (CommRingCat.of B') ⟶ S)
    (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
    (β : ofOver (Over.mk σ) ⟶ Y) [FiniteType β],
    CommSq α (specMapOver π σ) f β →
      ∃ γ : ofOver (Over.mk σ) ⟶ X, specMapOver π σ ≫ γ = α ∧ γ ≫ f = β

/-- Unfolding of `HasFiniteTypeSmallExtensionLifting`: every solid square
against a small extension whose bottom arrow is of finite type admits a lift. -/
theorem hasFiniteTypeSmallExtensionLifting_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    HasFiniteTypeSmallExtensionLifting f ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B] (π : B' →+* B) [π.IsSmallExtension]
        (σ : Spec (CommRingCat.of B') ⟶ S)
        (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
        (β : ofOver (Over.mk σ) ⟶ Y) [FiniteType β],
        CommSq α (specMapOver π σ) f β →
          ∃ γ : ofOver (Over.mk σ) ⟶ X, specMapOver π σ ≫ γ = α ∧ γ ≫ f = β :=
  sorry

/-- A locally finite-type morphism of algebraic spaces to a locally Noetherian
target is smooth if and only if every solid square against a small extension
whose bottom arrow is of finite type admits a lift. -/
theorem smooth_iff_smallExtensionLifting {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    Smooth f ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B] (π : B' →+* B) [π.IsSmallExtension]
        (σ : Spec (CommRingCat.of B') ⟶ S)
        (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
        (β : ofOver (Over.mk σ) ⟶ Y) [FiniteType β],
        CommSq α (specMapOver π σ) f β →
          ∃ γ : ofOver (Over.mk σ) ⟶ X, specMapOver π σ ≫ γ = α ∧ γ ≫ f = β :=
  sorry

/-- A locally finite-type morphism of algebraic spaces to a locally Noetherian
target is smooth if and only if it has the finite-type small-extension lifting
property. -/
theorem smooth_iff_hasFiniteTypeSmallExtensionLifting {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    Smooth f ↔ HasFiniteTypeSmallExtensionLifting f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
