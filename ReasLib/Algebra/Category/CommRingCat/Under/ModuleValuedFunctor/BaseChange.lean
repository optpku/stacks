module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable {A A' : CommRingCat.{u}}

namespace ModuleValuedFunctor

/-- Restriction of a module-valued functor along a morphism of commutative rings. -/
noncomputable def restrictAlong (f : A ⟶ A') :
    bundled.{u, u} A ⥤ bundled.{u, u} A' where
  obj F :=
    { obj := fun B ↦ F.obj ((Under.map f).obj B)
      map := fun g ↦ F.map ((Under.map f).map g)
      map_id := sorry
      map_comp := sorry }
  map φ :=
    { app := fun B ↦ φ.app ((Under.map f).obj B)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

end ModuleValuedFunctor

/-- Adequacy is preserved by precomposition with pushout along a ring morphism when
the presentation functors are compatible with restriction of scalars. -/
theorem Adequate.precompPushout
    (f : A ⟶ A')
    (underline : ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (underline' : ModuleCat.{u} A' ⥤ (Under A' ⥤ AddCommGrpCat.{u}))
    (compatibility :
      underline' ⋙
          (Functor.whiskeringLeft (Under A) (Under A') AddCommGrpCat.{u}).obj
            (Under.pushout f) ≅
        ModuleCat.restrictScalars f.hom ⋙ underline)
    {F' : Under A' ⥤ AddCommGrpCat.{u}}
    (hF' : Adequate A' underline' F') :
    Adequate A underline
      ((Functor.whiskeringLeft (Under A) (Under A') AddCommGrpCat.{u}).obj
        (Under.pushout f) |>.obj F') := sorry

/-- The adequacy of a functor is preserved by restriction along a morphism of
commutative rings when its kernel presentations are identified by extension of
scalars. -/
theorem Adequate.precompMap
    (f : A ⟶ A')
    (underline : ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (underline' : ModuleCat.{u} A' ⥤ (Under A' ⥤ AddCommGrpCat.{u}))
    (compatibility :
      underline ⋙
          (Functor.whiskeringLeft (Under A') (Under A) AddCommGrpCat.{u}).obj
            (Under.map f) ≅
        ModuleCat.extendScalars f.hom ⋙ underline')
    {F : Under A ⥤ AddCommGrpCat.{u}}
    (hF : Adequate A underline F) :
    Adequate A' underline'
      ((Functor.whiskeringLeft (Under A') (Under A) AddCommGrpCat.{u}).obj
        (Under.map f) |>.obj F) := sorry
