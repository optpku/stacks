module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity

/-!
# Comparison maps for relative differentials of schemes

This leaf records the sectionwise specifications for pullback and transitivity
maps of relative differentials. The specifications do not choose a comparison
map: existence and exactness belong to the geometric hypotheses of each
application.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}}

/-- A map from the pullback of `Ω[g]` to `Ω[h]` has the pullback-differentials specification
when its adjoint sends the universal differential of a section to the universal differential of
its pullback. -/
def pullbackRelativeDifferentialsMapSpec
    (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (τ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[h.toShHom]) : Prop :=
  RingedSpace.Hom.Differentials.IsComparison τ

/-- A map from `Ω[f ≫ g]` to `Ω[f]` has the transitivity-projection specification when it
sends each universal differential to the corresponding relative differential over `Y`. -/
def relativeDifferentialsTransitivityProjectionSpec
    (f : X ⟶ Y) (g : Y ⟶ S)
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  RingedSpace.Hom.Differentials.Transitivity.IsProjection
    f.toShHom g.toShHom ψ

/-- A pair of maps has the relative-differentials transitivity specifications when its first
map is the pullback comparison for `f ≫ g` and its second map is the canonical projection to
relative differentials over `Y`. -/
def relativeDifferentialsTransitivityMapSpecs
    (f : X ⟶ Y) (g : Y ⟶ S)
    (φ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[g.toShHom] ⟶ Ω[(f ≫ g).toShHom])
    (ψ : Ω[(f ≫ g).toShHom] ⟶ Ω[f.toShHom]) : Prop :=
  pullbackRelativeDifferentialsMapSpec f g (f ≫ g) φ ∧
    relativeDifferentialsTransitivityProjectionSpec f g ψ

end AlgebraicGeometry.Scheme
