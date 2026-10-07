module

public import Mathlib.CategoryTheory.Endomorphism
public import stacks_project.Chap98.Lemma_98_21_1
public import stacks_project.Chap98.Lemma_98_21_2_Functor

/-!
# Infinitesimal and tangent maps along a 1-morphism

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces
A-linear maps on `Inf_x(M)` and `T_x(M)` by the functoriality of lift
categories along the identity square of `A[M] ⟶ A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids (fiberFunctor reindexCompare)
open FiberedCategoryOver.Groupoids renaming liftFunctor → cfgLiftFunctor
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
variable {A : CommRingCat.{u}} {σA : Spec A ⟶ S}

/-- The identity-square lift functor of a 1-morphism along `A[M] ⟶ A`. -/
def alongLiftFunctor (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) ⥤
      liftCat ((fiberFunctor F (Over.mk σA)).obj x)
        (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  cfgLiftFunctor.onId F
    (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) x

/-- `alongLiftFunctor` is `liftFunctor.onId` along the coefficient projection of `A[M]`. -/
theorem alongLiftFunctor_eq (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    alongLiftFunctor F x M =
      cfgLiftFunctor.onId F
        (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) x := sorry

/-- Comparison identifying `F` of the trivial deformation of `x` with the trivial
deformation of `F(x)`. -/
def reindexCompareIso (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    (fiberFunctor F (Over.mk (specTrivSqZero σA M))).obj (trivialDeformation x M) ≅
      trivialDeformation ((fiberFunctor F (Over.mk σA)).obj x) M :=
  asIso (reindexCompare F (specOverInl σA M) x)

/-- The forward component of `reindexCompareIso` is `reindexCompare`. -/
theorem reindexCompareIso_hom (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    (reindexCompareIso F x M).hom = reindexCompare F (specOverInl σA M) x := sorry

/-- Push an infinitesimal automorphism of the trivial deformation of `x` along a
1-morphism, using `fiberFunctor` on the automorphism and the identity-square
comparison `reindexCompareIso`. -/
def infAlongType (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A)
    (α : infType x M) : infType ((fiberFunctor F (Over.mk σA)).obj x) M :=
  let e := reindexCompareIso F x M
  let Fα := (fiberFunctor F (Over.mk (specTrivSqZero σA M))).mapAut
    (trivialDeformation x M) α.1
  ⟨e.symm ≪≫ Fα ≪≫ e, sorry⟩

/-- The `A`-linear map `Inf_x(M) ⟶ Inf_{F(x)}(M)` induced by a 1-morphism. -/
def infAlong (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (infFunctor x).obj M ⟶
      (infFunctor ((fiberFunctor F (Over.mk σA)).obj x)).obj M :=
  ConcreteCategory.ofHom
    { toFun := infAlongType F x M
      map_add' := sorry
      map_smul' := sorry }

/-- `infAlong` acts by `infAlongType` on infinitesimal automorphisms of the
trivial deformation. -/
theorem infAlong_apply (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : (infFunctor x).obj M) :
    infAlong F x M α = infAlongType F x M α := sorry

/-- Well-definedness of isomorphism classes of lifts under `alongLiftFunctor`. -/
theorem alongLiftFunctor_lifts_wd (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) {a b : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)}
    (h : Nonempty (a ≅ b)) :
    lifts.mk ((alongLiftFunctor F x M).obj a) =
      lifts.mk ((alongLiftFunctor F x M).obj b) := sorry

/-- The map `Lift(x, A[M]) → Lift(F(x), A[M])` of isomorphism classes induced by a
1-morphism. -/
def tangentAlongType (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) →
      lifts ((fiberFunctor F (Over.mk σA)).obj x)
        (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  Quotient.lift (fun a ↦ lifts.mk ((alongLiftFunctor F x M).obj a))
    (fun _ _ h ↦ alongLiftFunctor_lifts_wd F x M h)

/-- The `A`-linear map `T_x(M) ⟶ T_{F(x)}(M)` induced by a 1-morphism. -/
def tangentAlong (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (tangentFunctor x).obj M ⟶
      (tangentFunctor ((fiberFunctor F (Over.mk σA)).obj x)).obj M :=
  ConcreteCategory.ofHom
    { toFun t :=
        (tangentForget ((fiberFunctor F (Over.mk σA)).obj x) M).symm
          (tangentAlongType F x M (tangentForget x M t))
      map_add' := sorry
      map_smul' := sorry }

/-- `tangentAlong` is `tangentAlongType` after identifying `T` with lifts. -/
theorem tangentAlong_apply (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (t : (tangentFunctor x).obj M) :
    tangentAlong F x M t =
      (tangentForget ((fiberFunctor F (Over.mk σA)).obj x) M).symm
        (tangentAlongType F x M (tangentForget x M t)) := sorry

/-- Forgetting `T` after `tangentAlong` recovers `tangentAlongType` of the
underlying lift. -/
theorem tangentForget_tangentAlong (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (t : (tangentFunctor x).obj M) :
    tangentForget ((fiberFunctor F (Over.mk σA)).obj x) M (tangentAlong F x M t) =
      tangentAlongType F x M (tangentForget x M t) := sorry

end AlgebraicGeometry.GroupoidsOver
