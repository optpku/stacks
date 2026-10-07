module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.BaseChange
public import Mathlib.Algebra.Category.Ring.Under.Basic

@[expose] public section

open CategoryTheory

universe u

variable {A A' : CommRingCat.{u}}

namespace ModuleValuedFunctor

/-- Evaluating restriction along `f` at `F` and `B` agrees with evaluating `F` on
the underlying `A`-algebra obtained from `B`. -/
theorem restrictAlong_obj_obj (f : A ⟶ A') (F : ModuleValuedFunctor.{u, u} A)
    (B : Under A') :
    ((restrictAlong f).obj F).obj B = F.obj ((Under.map f).obj B) := sorry

/-- Restriction along `f` evaluates a morphism at the underlying `A`-algebra. -/
theorem restrictAlong_map_app (f : A ⟶ A') {F G : bundled.{u, u} A}
    (φ : F ⟶ G) (B : Under A') :
    ((restrictAlong f).map φ).app B = φ.app ((Under.map f).obj B) := sorry

/-- The underlying additive-group functor of a restricted module-valued functor is
the precomposition of the original underlying functor with `Under.map f`. -/
theorem restrictAlong_toFunctor (f : A ⟶ A') (F : ModuleValuedFunctor.{u, u} A) :
    ((restrictAlong f).obj F).toFunctor = Under.map f ⋙ F.toFunctor := sorry

end ModuleValuedFunctor

namespace CategoryTheory.Under

/-- The natural transformation induced by the unit of the adjunction
`Under.pushout f ⊣ Under.map f`. -/
noncomputable def baseChangeUnit (f : A ⟶ A') (F : Under A ⥤ AddCommGrpCat.{u}) :
    F ⟶ (Under.pushout f ⋙ Under.map f) ⋙ F where
  app B := F.map ((Under.mapPushoutAdj f).unit.app B)
  naturality := sorry

/-- The component of `baseChangeUnit` at an `A`-algebra `B`. -/
theorem baseChangeUnit_app (f : A ⟶ A') (F : Under A ⥤ AddCommGrpCat.{u})
    (B : Under A) :
    (baseChangeUnit f F).app B = F.map ((Under.mapPushoutAdj f).unit.app B) := sorry

/-- The alternating difference of the two maps from the first to the second
base change induced by the adjunction unit. -/
noncomputable def baseChangeDifferential
    (f : A ⟶ A') (F : Under A ⥤ AddCommGrpCat.{u}) :
    (Under.pushout f ⋙ Under.map f) ⋙ F ⟶
      (Under.pushout f ⋙ Under.map f) ⋙ (Under.pushout f ⋙ Under.map f) ⋙ F where
  app B :=
    (F.map ((Under.mapPushoutAdj f).unit.app ((Under.pushout f ⋙ Under.map f).obj B)) :
      F.obj ((Under.pushout f ⋙ Under.map f).obj B) ⟶
        F.obj ((Under.pushout f ⋙ Under.map f).obj
          ((Under.pushout f ⋙ Under.map f).obj B))) -
      (F.map ((Under.pushout f ⋙ Under.map f).map
        ((Under.mapPushoutAdj f).unit.app B)) :
          F.obj ((Under.pushout f ⋙ Under.map f).obj B) ⟶
            F.obj ((Under.pushout f ⋙ Under.map f).obj
              ((Under.pushout f ⋙ Under.map f).obj B)))
  naturality := sorry

/-- The component of `baseChangeDifferential` at an `A`-algebra `B`. -/
theorem baseChangeDifferential_app
    (f : A ⟶ A') (F : Under A ⥤ AddCommGrpCat.{u}) (B : Under A) :
    (baseChangeDifferential f F).app B =
      (F.map ((Under.mapPushoutAdj f).unit.app ((Under.pushout f ⋙ Under.map f).obj B)) :
        F.obj ((Under.pushout f ⋙ Under.map f).obj B) ⟶
          F.obj ((Under.pushout f ⋙ Under.map f).obj
            ((Under.pushout f ⋙ Under.map f).obj B))) -
        (F.map ((Under.pushout f ⋙ Under.map f).map
          ((Under.mapPushoutAdj f).unit.app B)) :
            F.obj ((Under.pushout f ⋙ Under.map f).obj B) ⟶
              F.obj ((Under.pushout f ⋙ Under.map f).obj
                ((Under.pushout f ⋙ Under.map f).obj B))) := sorry

/-- The composite of the base-change unit and differential is zero. -/
theorem baseChangeUnit_comp_differential
    (f : A ⟶ A') (F : Under A ⥤ AddCommGrpCat.{u}) :
    baseChangeUnit f F ≫ baseChangeDifferential f F = 0 := sorry

end CategoryTheory.Under
