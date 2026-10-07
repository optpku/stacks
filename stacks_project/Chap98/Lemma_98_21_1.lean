module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_21_1_Lift
public import stacks_project.Chap98.Lemma_98_21_1_Functor
import Mathlib.Tactic.CrossRefAttribute

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
open FiberedCategoryOver.Groupoids (fiberFunctor reindexCompare reindexCompCompare)
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

/-- Lemma 98.21.1 (1). A 1-morphism `F : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf`, a commutative square of `S`-algebras, objects `x` over `Spec(A)` and
`y` over `Spec(B)`, and a fibre morphism `φ : F(x)|_Spec(B) ⟶ y` induce a canonical
functor `Lift(x, A') ⥤ Lift(y, B')`. -/
@[stacks 07Y7]
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

/-- Fibre comparison from the direct restriction of `(G ∘ F)(x')` along `specOverHom u`
to the identity pullback used by `onId G`. -/
def liftFunctor.compFibre {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
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
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y)
    (a : liftCat x fA hfA) :
    ((liftFunctor (F ≫ G) fA hfA fB hfB v hv u hu sq x
        ((fiberFunctor G (Over.mk σB)).obj y)
        (cfgLiftFunctor.connect F G (specOverHom v hv) φ)).obj a).codomain ⟶
      ((liftFunctor F fA hfA fB hfB v hv u hu sq x y φ ⋙
        cfgLiftFunctor.onId G (specOverHom fB hfB) y).obj a).codomain :=
  ⟨(reindexCompCompare F G (specOverHom u hu) a.codomain).1 ≫
      (inv (reindexCompare G (specOverHom u hu)
        ((fiberFunctor F (Over.mk σA')).obj a.codomain))).1 ≫
      (Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) (Over.mk σB')
        ((fiberFunctor G (Over.mk σB')).obj
          ((liftFunctor F fA hfA fB hfB v hv u hu sq x y φ).obj a).codomain)).hom.1,
    sorry⟩

/-- Inverse fibre comparison for `liftFunctor.compFibre`. -/
def liftFunctor.compFibreInv {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
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
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y)
    (a : liftCat x fA hfA) :
    ((liftFunctor F fA hfA fB hfB v hv u hu sq x y φ ⋙
        cfgLiftFunctor.onId G (specOverHom fB hfB) y).obj a).codomain ⟶
      ((liftFunctor (F ≫ G) fA hfA fB hfB v hv u hu sq x
        ((fiberFunctor G (Over.mk σB)).obj y)
        (cfgLiftFunctor.connect F G (specOverHom v hv) φ)).obj a).codomain :=
  ⟨(Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) (Over.mk σB')
        ((fiberFunctor G (Over.mk σB')).obj
          ((liftFunctor F fA hfA fB hfB v hv u hu sq x y φ).obj a).codomain)).inv.1 ≫
      (reindexCompare G (specOverHom u hu)
        ((fiberFunctor F (Over.mk σA')).obj a.codomain)).1 ≫
      (inv (reindexCompCompare F G (specOverHom u hu) a.codomain)).1,
    sorry⟩

/-- `liftFunctor.compFibre` is the composite of reindexing comparisons with the identity
cleavage component. -/
theorem liftFunctor.compFibre_spec {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
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
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y)
    (a : liftCat x fA hfA) :
    (liftFunctor.compFibre F G fA hfA fB hfB v hv u hu sq x y φ a).1 =
      (reindexCompCompare F G (specOverHom u hu) a.codomain).1 ≫
        (inv (reindexCompare G (specOverHom u hu)
          ((fiberFunctor F (Over.mk σA')).obj a.codomain))).1 ≫
        (Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) (Over.mk σB')
          ((fiberFunctor G (Over.mk σB')).obj
            ((liftFunctor F fA hfA fB hfB v hv u hu sq x y φ).obj a).codomain)).hom.1 := sorry

/-- `liftFunctor.compFibreInv` reverses `liftFunctor.compFibre` along the selected identity
cleavage comparison. -/
theorem liftFunctor.compFibreInv_spec {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
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
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y)
    (a : liftCat x fA hfA) :
    (liftFunctor.compFibreInv F G fA hfA fB hfB v hv u hu sq x y φ a).1 =
      (Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) (Over.mk σB')
          ((fiberFunctor G (Over.mk σB')).obj
            ((liftFunctor F fA hfA fB hfB v hv u hu sq x y φ).obj a).codomain)).inv.1 ≫
        (reindexCompare G (specOverHom u hu)
          ((fiberFunctor F (Over.mk σA')).obj a.codomain)).1 ≫
        (inv (reindexCompCompare F G (specOverHom u hu) a.codomain)).1 := sorry

/-- Lemma 98.21.1 (2). The functor of lift categories is compatible with composition of
1-morphisms of categories fibred in groupoids. -/
@[stacks 07Y7]
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
  NatIso.ofComponents
    (fun a ↦
      { hom := UnderLift.homMk
          (liftFunctor.compFibre F G fA hfA fB hfB v hv u hu sq x y φ a) sorry
        inv := UnderLift.homMk
          (liftFunctor.compFibreInv F G fA hfA fB hfB v hv u hu sq x y φ a) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- The forward component of composition compatibility is the selected cleavage comparison. -/
theorem liftFunctor_comp_hom_app {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
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
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y)
    (a : liftCat x fA hfA) :
    ((liftFunctor_comp F G fA hfA fB hfB v hv u hu sq x y φ).hom.app a).val =
      liftFunctor.compFibre F G fA hfA fB hfB v hv u hu sq x y φ a := sorry

end AlgebraicGeometry.GroupoidsOver
