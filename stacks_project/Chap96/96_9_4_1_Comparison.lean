module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Comparison

/-!
# Small-étale comparison morphisms of module sheaves on a CFG

A morphism `φ : x ⟶ y` in a category fibred in groupoids over `(Sch/S)_fppf`
induces a comparison morphism of `𝒪_{U_étale}`-modules
`c_φ : a_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` from the cartesian fill-in of
the pullback square of `a = (X.p.map φ).left`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The selected cartesian lift of an object along a small-étale neighborhood. -/
abbrev cartesianLift (x : X.total) (W : (X.p.obj x).left.Etale) : X.total :=
  (smallEtaleEval x).obj W

/-- A morphism of small-étale neighborhoods induces a morphism of cartesian lifts. -/
abbrev cartesianLiftMap (x : X.total) {W' W : (X.p.obj x).left.Etale}
    (g : W' ⟶ W) : cartesianLift x W' ⟶ cartesianLift x W :=
  (smallEtaleEval x).map g

/-- The cartesian fill-in of the small-étale pullback square over a total-category morphism. -/
abbrev fillIn {x y : X.total} (φ : x ⟶ y) (V' : (X.p.obj y).left.Etale) :
    cartesianLift x ((Scheme.smallEtalePullback (X.p.map φ).left).obj V') ⟶
      cartesianLift y V' :=
  comparisonPushHom φ V'

#check (AlgebraicGeometry.GroupoidsOver.moduleComparison :
  {S : Scheme.{u}} → {X : GroupoidsOver S} → {x y : X.total} →
    (φ : x ⟶ y) → (F : SheafOfModules.{u} (etaleStructureSheaf X)) →
      ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePullback.{u}).obj
          ((restrictModulesToSmallEtale X y).obj F) ⟶
        (restrictModulesToSmallEtale X x).obj F)

end AlgebraicGeometry.GroupoidsOver
