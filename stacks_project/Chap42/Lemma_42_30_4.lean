module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FirstChern.Relative

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- Lemma 42.30.4: if `i = Scheme.zeroSchemeι ℒ s` is the inclusion of the zero
scheme of `s`, then Gysin pullback by `i` commutes with first-Chern-class intersection
after pulling back the invertible module. Both sides have degree `k - 2`. -/
@[stacks 0B72] #check (AlgebraicGeometry.ChowGroup.gysin_firstChernClassCap :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (𝒩 : X.left.Modules) [Scheme.Modules.Invertible 𝒩] (k : ℤ)
    (α : RelativeChow δ X k),
    gysin δ X ℒ s (k - 1) (firstChernClassCap δ X 𝒩 k α) =
      firstChernClassCap δ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom))
        ((Scheme.Modules.pullback
          (Over.homMk (Scheme.zeroSchemeι ℒ s) :
            Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left).obj 𝒩) (k - 1)
        (gysin δ X ℒ s k α))

end AlgebraicGeometry.ChowGroup
