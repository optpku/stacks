module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.DifferentialExterior
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible.Closed

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.Ramification

/-- The comparison on relative differentials induced by a morphism of schemes over `S`. -/
def differentialMap {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) :
    (RingedSpace.Hom.pullback f.left.toShHom).obj Ω[X.hom.toShHom] ⟶
      Ω[Y.hom.toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((CommSq.mk (f.w.trans (Category.comp_id _).symm) :
        CommSq f.left Y.hom X.hom (𝟙 S)).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The relative differential map is the canonical comparison attached to the square over `S`. -/
theorem differentialMap_spec {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) :
    differentialMap f =
      RingedSpace.Hom.Differentials.comparison
        ((CommSq.mk (f.w.trans (Category.comp_id _).symm) :
            CommSq f.left Y.hom X.hom (𝟙 S)).map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace)) := sorry

/-- The map on degree-`n` exterior powers induced by the relative differential map. -/
def topDifferentialMap {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) (n : ℕ) :
    (Λ[n] ((RingedSpace.Hom.pullback f.left.toShHom).obj Ω[X.hom.toShHom])) ⟶
      (Λ[n] Ω[Y.hom.toShHom]) :=
  RingedSpace.ExteriorPower.map (differentialMap f) n

/-- The top differential map is the exterior power of the relative differential comparison. -/
theorem topDifferentialMap_def {S : Scheme.{u}} {X Y : Over S}
    (f : Y ⟶ X) (n : ℕ) :
    topDifferentialMap f n =
      RingedSpace.ExteriorPower.map (differentialMap f) n := sorry

/-- The internal-Hom line in which the top relative differential is a section. -/
def line {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) (n : ℕ) : Y.left.Modules :=
  (ihom (Λ[n] ((RingedSpace.Hom.pullback f.left.toShHom).obj Ω[X.hom.toShHom]))).obj
    (Λ[n] Ω[Y.hom.toShHom])

/-- The ramification line is represented by the internal Hom between the top differential
modules. -/
theorem line_def {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) (n : ℕ) :
    line f n =
      (ihom (Λ[n] ((RingedSpace.Hom.pullback f.left.toShHom).obj Ω[X.hom.toShHom]))).obj
        (Λ[n] Ω[Y.hom.toShHom]) := sorry

/-- The canonical section obtained by currying the top relative differential map. -/
def «section» {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) (n : ℕ) :
    (line f n).sections :=
  (line f n).unitHomEquiv
    ((SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := _root_.Opens.grothendieckTopology Y.left.toTopCat)
      (𝒪 := Y.left.𝒪)).hom ≫
        (MonoidalClosed.curry' (topDifferentialMap f n) :
          𝟙_ (Y.left.Modules) ⟶ line f n))

/-- The ramification section is the section corresponding to the curried top differential. -/
theorem section_def {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) (n : ℕ) :
    «section» f n =
      (line f n).unitHomEquiv
        ((SheafOfModules.RingedSite.unitIsoTensorUnit
          (J := _root_.Opens.grothendieckTopology Y.left.toTopCat)
          (𝒪 := Y.left.𝒪)).hom ≫
            (MonoidalClosed.curry' (topDifferentialMap f n) :
              𝟙_ (Y.left.Modules) ⟶ line f n)) := sorry

/-- For smooth source and target of common relative dimension `n`, the ramification line is
invertible. -/
instance instIsInvertibleLine {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] [SmoothOfRelativeDimension n Y.hom] :
    Scheme.Modules.Invertible (line f n) := sorry

end AlgebraicGeometry.Scheme.Hom.Ramification
