module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineBundle

/-!
# Flat pullback along affine-space bundles

Flat pullback along a morphism locally isomorphic over its target to relative affine space
is bijective. Local triviality supplies its geometric prerequisites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- If a flat morphism of relative dimension `r` is locally over its target isomorphic to
relative affine `r`-space, then its pullback on Chow groups is surjective. -/
theorem flatPullback_surjective_of_localAffineSpace
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) : Function.Surjective (flatPullback δ X Y f r k) := sorry

/-- If a flat morphism of relative dimension `r` is locally over its target isomorphic to
relative affine `r`-space, then its pullback on Chow groups is injective. -/
theorem flatPullback_injective_of_localAffineSpace
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) : Function.Injective (flatPullback δ X Y f r k) := sorry

/-- A flat morphism of relative dimension `r` locally isomorphic over its target to relative
affine `r`-space induces a bijective pullback on Chow groups in every degree. -/
theorem flatPullback_bijective_of_localAffineSpace
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) : Function.Bijective (flatPullback δ X Y f r k) :=
  ⟨flatPullback_injective_of_localAffineSpace δ X Y f r h_local k,
    flatPullback_surjective_of_localAffineSpace δ X Y f r h_local k⟩

/-- Pullback on Chow groups along an affine-space bundle, with flatness, relative dimension,
and local finite type of its source supplied by local triviality. -/
noncomputable def affineBundlePullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (r : ℕ)
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) :=
  @flatPullback S inferInstance δ inferInstance X Y
    (Scheme.Hom.locallyOfFiniteType_over_of_localAffineSpace X Y f r h_local)
    inferInstance f r (Scheme.Hom.flat_of_localAffineSpace f.left r h_local)
    (Scheme.Hom.relativeDimension_of_localAffineSpace f.left r h_local) k

/-- Affine-space bundle pullback agrees with flat pullback whenever the latter's geometric
prerequisites are supplied independently. -/
theorem affineBundlePullback_eq_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) : affineBundlePullback δ X Y f r h_local k = flatPullback δ X Y f r k := rfl

/-- An affine-space bundle over a scheme locally of finite type over a universally catenary
dimensioned base induces a bijective pullback on Chow groups in every integer degree. -/
theorem affineBundlePullback_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (r : ℕ)
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) : Function.Bijective (affineBundlePullback δ X Y f r h_local k) :=
  @flatPullback_bijective_of_localAffineSpace S inferInstance δ inferInstance X Y
    (Scheme.Hom.locallyOfFiniteType_over_of_localAffineSpace X Y f r h_local)
    inferInstance f r (Scheme.Hom.flat_of_localAffineSpace f.left r h_local)
    (Scheme.Hom.relativeDimension_of_localAffineSpace f.left r h_local) h_local k

end AlgebraicGeometry.ChowGroup
