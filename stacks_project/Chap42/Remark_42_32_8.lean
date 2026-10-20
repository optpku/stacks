module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.AffineBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Remark 42.32.8: a morphism locally isomorphic over its target to relative affine
`r`-space induces an isomorphism on Chow groups, shifting degree by `r`. -/
@[stacks 0GUB] #check
  (AlgebraicGeometry.ChowGroup.affineBundlePullback_bijective :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (r : ℕ)
      (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
        Nonempty (Over.mk (f.left ∣_ U) ≅
          Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
      (k : ℤ),
      Function.Bijective
        (AlgebraicGeometry.ChowGroup.affineBundlePullback δ X Y f r h_local k))
