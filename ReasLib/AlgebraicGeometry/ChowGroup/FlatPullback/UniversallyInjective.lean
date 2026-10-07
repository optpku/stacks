module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

/-!
# Universally injective Chow pullback

This module records flat morphisms whose pullback on Chow groups is injective
after every base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ChowGroup

/-- A flat morphism has universally injective Chow pullback if its pullback along every morphism
of schemes over the base is injective in every degree. -/
def UniversallyInjectivePullback
    {S X P : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S)
    (π : P ⟶ X) (d : ℕ) [Flat π] [Scheme.Hom.RelativeDimension π d] : Prop :=
  ∀ (Y : Over S) [LocallyOfFiniteType Y.hom] (f : Y ⟶ Over.mk p) (k : ℤ),
    Function.Injective
      (@flatPullback S (inferInstance : UniversallyCatenary S) δ
        (inferInstance : IsDimensionFunction δ)
        (Over.mk (pullback.snd π f.left ≫ Y.hom)) Y
        (locallyOfFiniteType_comp (pullback.snd π f.left) Y.hom)
        (inferInstance : LocallyOfFiniteType Y.hom)
        (Over.homMk (pullback.snd π f.left)) d
        (inferInstance : Flat (pullback.snd π f.left))
        (inferInstance : Scheme.Hom.RelativeDimension (pullback.snd π f.left) d) k)

/-- Universal Chow-pullback injectivity specializes to a chosen base change and degree. -/
theorem UniversallyInjectivePullback.injective
    {S X P : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S)
    (π : P ⟶ X) (d : ℕ) [Flat π] [Scheme.Hom.RelativeDimension π d]
    (hπ : UniversallyInjectivePullback δ p π d)
    (Y : Over S) [LocallyOfFiniteType Y.hom] (f : Y ⟶ Over.mk p) (k : ℤ) :
    Function.Injective
      (@flatPullback S (inferInstance : UniversallyCatenary S) δ
        (inferInstance : IsDimensionFunction δ)
        (Over.mk (pullback.snd π f.left ≫ Y.hom)) Y
        (locallyOfFiniteType_comp (pullback.snd π f.left) Y.hom)
        (inferInstance : LocallyOfFiniteType Y.hom)
        (Over.homMk (pullback.snd π f.left)) d
        (inferInstance : Flat (pullback.snd π f.left))
        (inferInstance : Scheme.Hom.RelativeDimension (pullback.snd π f.left) d) k) := sorry

end AlgebraicGeometry.ChowGroup
