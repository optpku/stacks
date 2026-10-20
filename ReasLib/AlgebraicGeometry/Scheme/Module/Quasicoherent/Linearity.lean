module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace toRingedSpace

/-- The identity-on-data functor from scheme modules to ringed-space modules is additive. -/
instance additive (X : Scheme.{u}) : (Scheme.Modules.toRingedSpace X).Additive := sorry

end toRingedSpace

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The action of `R` on scheme modules induced by a structure morphism
`f : X ⟶ Spec (CommRingCat.of R)`, expressed through the categorical center. -/
noncomputable def baseCenterHom (f : X ⟶ Spec (CommRingCat.of R)) :
    R →+* CatCenter X.Modules where
  toFun r :=
    { app := fun M ↦
        fromRingedSpaceMap X
          (((((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
            (Scheme.Hom.globalSectionsMap f)) r).app) (toRingedSpaceObj X M))
      naturality := sorry }
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The `R`-linear structure on `X.Modules` induced by
`f : X ⟶ Spec (CommRingCat.of R)`. -/
noncomputable def baseLinear (f : X ⟶ Spec (CommRingCat.of R)) : Linear R X.Modules :=
  Linear.ofRingMorphism (baseCenterHom f)

/-- The relative scalar structure on scheme modules is induced by the transported
global-section action. -/
theorem baseLinear_def (f : X ⟶ Spec (CommRingCat.of R)) :
    baseLinear f = Linear.ofRingMorphism (baseCenterHom f) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}

/-- The `R`-linear structure on quasicoherent modules induced by
`f : X ⟶ Spec (CommRingCat.of R)`. -/
noncomputable def baseLinear (f : X ⟶ Spec (CommRingCat.of R)) : Linear R (Scheme.QCoh X) :=
  @CategoryTheory.Linear.fullSubcategory X.Modules _ _ R _
    (Scheme.Modules.baseLinear f) (Scheme.quasiCoherentModuleProperty X)

/-- The relative scalar structure on quasicoherent modules is the full-subcategory
structure induced from all scheme modules. -/
theorem baseLinear_def (f : X ⟶ Spec (CommRingCat.of R)) :
    baseLinear f =
      @CategoryTheory.Linear.fullSubcategory X.Modules _ _ R _
        (Scheme.Modules.baseLinear f) (Scheme.quasiCoherentModuleProperty X) := sorry

/-- A functor of quasicoherent modules is linear over chosen maps to the same affine base
when it is additive and linear for the scalar structures induced by those maps. -/
class LinearOver (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) : Prop
    extends F.Additive,
      @Functor.Linear R _ (Scheme.QCoh X) (Scheme.QCoh Y) _ _ _ _
        (baseLinear x) (baseLinear y) F

/-- Relative linearity consists exactly of additivity and linearity for the two
base-induced scalar structures. -/
theorem linearOver_iff (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) :
    LinearOver x y F ↔
      F.Additive ∧
        @Functor.Linear R _ (Scheme.QCoh X) (Scheme.QCoh Y) _ _ _ _
          (baseLinear x) (baseLinear y) F := sorry

namespace LinearOver

/-- The identity functor is linear over a fixed affine-base structure morphism. -/
instance id (x : X ⟶ Spec (CommRingCat.of R)) :
    LinearOver x x (𝟭 (Scheme.QCoh X)) := sorry

/-- A composite of relatively linear functors is relatively linear. -/
theorem comp (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) (G : Scheme.QCoh Y ⥤ Scheme.QCoh Z)
    [LinearOver x y F] [LinearOver y z G] : LinearOver x z (F ⋙ G) := sorry

end LinearOver

end AlgebraicGeometry.Scheme.QCoh
