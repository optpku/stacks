module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Lifts

/-!
# Functoriality of categories of lifts

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf`, together with a
commutative square of `S`-algebras and a fibre morphism `φ : F(x)|_Spec(B) ⟶ y`,
induces a functor of categories of lifts. The construction is compatible with
composition of 1-morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids (fiberFunctor)
open FiberedCategoryOver.Groupoids renaming liftFunctor → cfgLiftFunctor
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The morphism in `Over S` induced by an `S`-algebra map. -/
def specOverHom {S : Scheme.{u}} {R T : CommRingCat.{u}}
    {σR : Spec R ⟶ S} {σT : Spec T ⟶ S}
    (f : T ⟶ R) (hf : Spec.map f ≫ σT = σR) :
    Over.mk σR ⟶ Over.mk σT :=
  Over.homMk (Spec.map f) hf

/-- `specOverHom f hf` is the `Over S` arrow with left component `Spec.map f`. -/
theorem specOverHom_left {S : Scheme.{u}} {R T : CommRingCat.{u}}
    {σR : Spec R ⟶ S} {σT : Spec T ⟶ S}
    (f : T ⟶ R) (hf : Spec.map f ≫ σT = σR) :
    (specOverHom f hf).left = Spec.map f := sorry

/-- A commutative square of `S`-algebras induces a commutative square in `Over S`. -/
theorem specOverHom_commSq {S : Scheme.{u}} {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB) :
    CommSq (specOverHom fB hfB) (specOverHom v hv)
      (specOverHom u hu) (specOverHom fA hfA) := sorry

/-- The category `Lift(x, A')` of lifts of a fibre object `x` over `Spec(A)` along an
`S`-algebra map `A' ⟶ A`. -/
abbrev liftCat {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) :=
  UnderLift X.p (specOverHom fA hfA) x

/-- `liftCat x fA hfA` is the fibered lift category of `x` along `specOverHom fA`. -/
theorem liftCat_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) :
    liftCat x fA hfA = UnderLift X.p (specOverHom fA hfA) x := sorry

/-- A 1-morphism `F : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf`, a commutative square of `S`-algebras, objects `x` over `Spec(A)` and
`y` over `Spec(B)`, and a fibre morphism `φ : F(x)|_Spec(B) ⟶ y` induce a canonical
functor `Lift(x, A') ⥤ Lift(y, B')`. -/
def liftFunctor {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y)
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : Y.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj Y.p (specOverHom v hv)
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y) :
    liftCat x fA hfA ⥤ liftCat y fB hfB :=
  cfgLiftFunctor F
    (specOverHom fA hfA) (specOverHom fB hfB) (specOverHom v hv) (specOverHom u hu)
    (specOverHom_commSq fA hfA fB hfB v hv u hu sq) φ

/-- The functor on categories of lifts over spectra is compatible with composition of
morphisms of categories fibred in groupoids. -/
def liftFunctor_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : Y.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj Y.p (specOverHom v hv)
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y) :
    liftFunctor (F ≫ G) fA hfA fB hfB v hv u hu sq x
        ((fiberFunctor G (Over.mk σB)).obj y)
        (cfgLiftFunctor.connect F G (specOverHom v hv) φ) ≅
      liftFunctor F fA hfA fB hfB v hv u hu sq x y φ ⋙
        cfgLiftFunctor.onId G (specOverHom fB hfB) y :=
  FiberedCategoryOver.Groupoids.liftFunctor_comp F G
    (specOverHom fA hfA) (specOverHom fB hfB) (specOverHom v hv) (specOverHom u hu)
    (specOverHom_commSq fA hfA fB hfB v hv u hu sq) φ

end AlgebraicGeometry.GroupoidsOver
