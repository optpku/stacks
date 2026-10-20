module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange

/-!
# Comparison of fibres along a morphism of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The comparison `X_T ⟶ Y_T` induced by `π : X ⟶ Y` over `B`. -/
def fiberComparison (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B) :
    fiber (π ≫ y) σ ⟶ fiber y σ :=
  pullback.map (π ≫ y) σ.hom y σ.hom π
    (𝟙 ((ofOverFunctor S).obj σ.left)) (𝟙 B) (Category.comp_id (π ≫ y))
    ((Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)

/-- The fibre comparison commutes with the projections to `X` and `Y`. -/
theorem fiberComparison_fst (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
      pullback.fst (π ≫ y) σ.hom ≫ π :=
  sorry

/-- The fibre comparison is the map of pullbacks induced by `π` and the identity
on the test scheme. -/
theorem fiberComparison_spec (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
        pullback.fst (π ≫ y) σ.hom ≫ π ∧
      fiberComparison π y σ ≫ pullback.snd y σ.hom =
        pullback.snd (π ≫ y) σ.hom :=
  sorry

/-- The square relating `X_T ⟶ X` to `Y_T ⟶ Y` along `π` is cartesian. -/
theorem fiberComparison_isPullback_fst (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B) :
    IsPullback (pullback.fst (π ≫ y) σ.hom) (fiberComparison π y σ)
      π (pullback.fst y σ.hom) :=
  sorry

/-- Fibrewise base change of an affine morphism `π` remains affine. -/
instance affine_fiberComparison (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B) [Affine π] :
    Affine (fiberComparison π y σ) :=
  Affine.of_isPullback (fiberComparison_isPullback_fst π y σ) inferInstance

/-- The fibre comparison induced by a closed immersion is a closed immersion. -/
instance isClosedImmersion_fiberComparison (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B) [IsClosedImmersion π] :
    IsClosedImmersion (fiberComparison π y σ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
