/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans

/-!
# Whiskering of displayed natural transformations

Displayed natural transformations support the same left, right, and horizontal compositions as
ordinary natural transformations.  The displayed component is explicit; only the dependent
naturality field is deferred in this statement-stage support layer.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u' v'' u''

namespace DisplayedNatTrans

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {C'' : Type u''} [Category.{v''} C'']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'}
variable {E' : DisplayedCategory C''}
variable {F G : C ⥤ C'} {H I : C' ⥤ C''}
variable {Phi : DisplayedFunctor D E F} {Psi : DisplayedFunctor D E G}
variable {Omega : DisplayedFunctor E E' H} {Chi : DisplayedFunctor E E' I}
variable {alpha : F ⟶ G} {beta : H ⟶ I}

/-- Right-whisker a displayed natural transformation by a displayed functor. -/
def whiskerRight (eta : DisplayedNatTrans Phi Psi alpha) (Omega : DisplayedFunctor E E' H) :
    DisplayedNatTrans (DisplayedFunctor.comp Phi Omega) (DisplayedFunctor.comp Psi Omega)
      (Functor.whiskerRight alpha H) where
  app x := Omega.map (eta.app x)
  naturality := sorry

/-- The component of a right-whiskered displayed transformation. -/
@[simp]
theorem whiskerRight_app (eta : DisplayedNatTrans Phi Psi alpha)
    (Omega : DisplayedFunctor E E' H) {X : C} (x : D.obj X) :
    (whiskerRight eta Omega).app x = Omega.map (eta.app x) := sorry

/-- Left-whisker a displayed natural transformation by a displayed functor. -/
def whiskerLeft
    {C₀ : Type u''} [Category.{v''} C₀] {D₀ : DisplayedCategory C₀}
    {K : C₀ ⥤ C} (Lambda : DisplayedFunctor D₀ D K)
    (eta : DisplayedNatTrans Phi Psi alpha) :
    DisplayedNatTrans (DisplayedFunctor.comp Lambda Phi) (DisplayedFunctor.comp Lambda Psi)
      (Functor.whiskerLeft K alpha) where
  app x := eta.app (Lambda.obj x)
  naturality := sorry

/-- The component of a left-whiskered displayed transformation. -/
@[simp]
theorem whiskerLeft_app
    {C₀ : Type u''} [Category.{v''} C₀] {D₀ : DisplayedCategory C₀}
    {K : C₀ ⥤ C} (Lambda : DisplayedFunctor D₀ D K)
    (eta : DisplayedNatTrans Phi Psi alpha) {X : C₀} (x : D₀.obj X) :
    (whiskerLeft Lambda eta).app x = eta.app (Lambda.obj x) := sorry

/-- Horizontal composition of displayed natural transformations. -/
def hcomp (eta : DisplayedNatTrans Phi Psi alpha)
    (theta : DisplayedNatTrans Omega Chi beta) :
    DisplayedNatTrans (DisplayedFunctor.comp Phi Omega) (DisplayedFunctor.comp Psi Chi)
      (alpha ◫ beta) where
  app x := E'.comp (theta.app (Phi.obj x)) (Chi.map (eta.app x))
  naturality := sorry

/-- The displayed component of horizontal composition. -/
@[simp]
theorem hcomp_app (eta : DisplayedNatTrans Phi Psi alpha)
    (theta : DisplayedNatTrans Omega Chi beta) {X : C} (x : D.obj X) :
    (hcomp eta theta).app x =
      E'.comp (theta.app (Phi.obj x)) (Chi.map (eta.app x)) := sorry

/-- Totalization commutes with right whiskering. -/
theorem total_whiskerRight (eta : DisplayedNatTrans Phi Psi alpha)
    (Omega : DisplayedFunctor E E' H) :
    total (whiskerRight eta Omega) =
      Functor.whiskerRight (total eta) (DisplayedFunctor.total Omega) := sorry

/-- Totalization commutes with left whiskering. -/
theorem total_whiskerLeft
    {C₀ : Type u''} [Category.{v''} C₀] {D₀ : DisplayedCategory C₀}
    {K : C₀ ⥤ C} (Lambda : DisplayedFunctor D₀ D K)
    (eta : DisplayedNatTrans Phi Psi alpha) :
    total (whiskerLeft Lambda eta) =
      Functor.whiskerLeft (DisplayedFunctor.total Lambda) (total eta) := sorry

/-- Totalization commutes with horizontal composition. -/
theorem total_hcomp (eta : DisplayedNatTrans Phi Psi alpha)
    (theta : DisplayedNatTrans Omega Chi beta) :
    total (hcomp eta theta) = total eta ◫ total theta := sorry

end DisplayedNatTrans

end CategoryTheory
