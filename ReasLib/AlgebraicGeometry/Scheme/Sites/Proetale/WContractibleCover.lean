module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.AffineWContractible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.WeaklyContractible
public import ReasLib.CategoryTheory.Sites.EnoughObjects

/-!
# Affine w-contractible covers in bounded big pro-étale sites

Every object of a bounded big pro-étale site admits a covering by affine
objects with w-contractible global sections that are weakly contractible in the site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.BigProetaleSite

/-- Every object of a bounded big pro-étale site admits a covering family whose
sources are affine, have w-contractible global sections, and are weakly contractible. -/
@[stacks 098I]
theorem exists_affine_wContractibleRing_cover
    (X : BigProetaleSite.{u}) (T : X.carrier) :
    ∃ 𝒰 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Presieve.ofArrows (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) ∈
          (@Pretopology.toPrecoverage _ _ X.hasPullbacks X.pretopology) T ∧
        ∀ i, IsAffine (X.toScheme.obj (𝒰.obj i).left) ∧
          IsWContractibleRing.{u, u} Γ(X.toScheme.obj (𝒰.obj i).left, ⊤) ∧
          X.toGrothendieck.IsWeaklyContractible (𝒰.obj i).left := sorry

/-- Every object of a bounded big pro-étale site admits a covering family whose
sources are affine and weakly contractible. -/
theorem exists_affine_weaklyContractible_cover
    (X : BigProetaleSite.{u}) (T : X.carrier) :
    ∃ 𝒰 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Presieve.ofArrows (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) ∈
          (@Pretopology.toPrecoverage _ _ X.hasPullbacks X.pretopology) T ∧
        ∀ i, IsAffine (X.toScheme.obj (𝒰.obj i).left) ∧
          X.toGrothendieck.IsWeaklyContractible (𝒰.obj i).left := sorry

/-- A bounded big pro-étale topology has enough affine objects whose global
sections are w-contractible rings. -/
theorem hasEnough_isAffine_isWContractibleRing (X : BigProetaleSite.{u}) :
    X.toGrothendieck.HasEnoughObjectsWithProperty
      (fun T ↦ IsAffine (X.toScheme.obj T) ∧
        IsWContractibleRing.{u, u} Γ(X.toScheme.obj T, ⊤)) := sorry

end AlgebraicGeometry.BigProetaleSite
