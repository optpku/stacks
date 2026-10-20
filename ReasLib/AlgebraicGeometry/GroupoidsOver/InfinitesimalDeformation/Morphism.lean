module

public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts
public import ReasLib.CategoryTheory.Fibered.Groupoids.Lifts
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation

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

variable {S : Scheme.{u}}
variable {A : CommRingCat.{u}} {σA : Spec A ⟶ S}

section Along

variable {X Y : GroupoidsOver S}
variable [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]

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
      (infFunctor ((fiberFunctor F (Over.mk σA)).obj x)).obj M := by
  let f : (infFunctor x).obj M → (infFunctor ((fiberFunctor F (Over.mk σA)).obj x)).obj M :=
    infAlongType F x M
  have laws : (∀ a b, f (a + b) = f a + f b) ∧
      (∀ (r : A) a, f (r • a) = r • f a) := by sorry
  exact ConcreteCategory.ofHom
    { toFun := f
      map_add' := laws.1
      map_smul' := laws.2 }

/-- `infAlong` acts by `infAlongType` on infinitesimal automorphisms of the
trivial deformation. -/
theorem infAlong_apply (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : (infFunctor x).obj M) :
    infAlong F x M α = infAlongType F x M α := sorry

/-- The map `Lift(x, A[M]) → Lift(F(x), A[M])` of isomorphism classes induced by a
1-morphism. -/
def tangentAlongType (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) →
      lifts ((fiberFunctor F (Over.mk σA)).obj x)
        (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  Quotient.lift (fun a ↦ lifts.mk ((cfgLiftFunctor.onId F
      (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) x).obj a))
    (by sorry)

/-- The `A`-linear map `T_x(M) ⟶ T_{F(x)}(M)` induced by a 1-morphism. -/
def tangentAlong (F : X ⟶ Y) (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (tangentFunctor x).obj M ⟶
      (tangentFunctor ((fiberFunctor F (Over.mk σA)).obj x)).obj M := by
  let f : (tangentFunctor x).obj M → (tangentFunctor ((fiberFunctor F (Over.mk σA)).obj x)).obj M :=
    fun t ↦
      (tangentForget ((fiberFunctor F (Over.mk σA)).obj x) M).symm
        (tangentAlongType F x M (tangentForget x M t))
  have laws : (∀ a b, f (a + b) = f a + f b) ∧
      (∀ (r : A) a, f (r • a) = r • f a) := by sorry
  exact ConcreteCategory.ofHom
    { toFun := f
      map_add' := laws.1
      map_smul' := laws.2 }

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

end Along

section Congruence

variable {X : GroupoidsOver S}

/-- Reindexing a fibre isomorphism along `Spec(A[M]) ⟶ Spec(A)`. -/
def trivialDeformationCongr {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    trivialDeformation x M ≅ trivialDeformation x' M := by
  let h := Chosen.reindexMap X.p (specOverInl σA M) φ.hom
  let i := Chosen.reindexMap X.p (specOverInl σA M) φ.inv
  have laws : h ≫ i = 𝟙 _ ∧ i ≫ h = 𝟙 _ := by sorry
  exact { hom := h, inv := i, hom_inv_id := laws.1, inv_hom_id := laws.2 }

/-- `trivialDeformationCongr` reindexes the supplied fibre isomorphism. -/
theorem trivialDeformationCongr_hom {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    (trivialDeformationCongr φ M).hom =
      Chosen.reindexMap X.p (specOverInl σA M) φ.hom := sorry

/-- Transport `Inf` along a fibre isomorphism over `Spec(A)`. -/
def infCongr [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    (infFunctor x).obj M ⟶ (infFunctor x').obj M := by
  let g (α : infType x M) :=
    (trivialDeformationCongr φ M).symm ≪≫ α.1 ≪≫ trivialDeformationCongr φ M
  let P := ∀ α : infType x M,
    (trivialDeformationLift x' M).hom ≫ Fiber.fiberInclusion.map (g α).hom =
      (trivialDeformationLift x' M).hom
  let f (h : P) : (infFunctor x).obj M → (infFunctor x').obj M :=
    fun α ↦ ⟨g α, h α⟩
  have laws : P ∧ ∀ h : P,
      (∀ a b, f h (a + b) = f h a + f h b) ∧
      (∀ (r : A) a, f h (r • a) = r • f h a) := by sorry
  exact ConcreteCategory.ofHom
    { toFun := f laws.1
      map_add' := (laws.2 laws.1).1
      map_smul' := (laws.2 laws.1).2 }

/-- `infCongr` conjugates the underlying automorphism by the trivial deformation
of the fibre isomorphism. -/
theorem infCongr_apply [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    (α : infType x M) :
    (infCongr φ M α).1 =
      (trivialDeformationCongr φ M).symm ≪≫ α.1 ≪≫ trivialDeformationCongr φ M :=
  sorry

/-- Transport `T` along a fibre isomorphism by precomposing lifts with the inverse. -/
def tangentCongrType {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    (a : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) :
    liftCat x' (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  ⟨Under.mk (Fiber.fiberInclusion.map φ.inv ≫ a.hom),
    by sorry⟩

/-- The `A`-linear map `T_x(M) ⟶ T_{x'}(M)` induced by a fibre isomorphism. -/
def tangentCongr [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    (tangentFunctor x).obj M ⟶ (tangentFunctor x').obj M := by
  let P := ∀ a b : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M),
    Nonempty (a ≅ b) →
      lifts.mk (tangentCongrType φ M a) = lifts.mk (tangentCongrType φ M b)
  let f (h : P) : (tangentFunctor x).obj M → (tangentFunctor x').obj M :=
    fun t ↦ (tangentForget x' M).symm
      (Quotient.lift (fun a ↦ lifts.mk (tangentCongrType φ M a)) h
        (tangentForget x M t))
  have laws : P ∧ ∀ h : P,
      (∀ a b, f h (a + b) = f h a + f h b) ∧
      (∀ (r : A) a, f h (r • a) = r • f h a) := by sorry
  exact ConcreteCategory.ofHom
    { toFun := f laws.1
      map_add' := (laws.2 laws.1).1
      map_smul' := (laws.2 laws.1).2 }

/-- `tangentCongr` precomposes the underlying lift with the inverse fibre
isomorphism. -/
theorem tangentCongr_apply [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    (t : (tangentFunctor x).obj M) :
    tangentForget x' M (tangentCongr φ M t) =
      Quotient.lift (fun a ↦ lifts.mk (tangentCongrType φ M a))
        (by
          intro a b h
          rcases h with ⟨e⟩
          let η : tangentCongrType φ M a ⟶ tangentCongrType φ M b :=
            UnderLift.homMk e.hom.val (by
              change (Fiber.fiberInclusion.map φ.inv ≫ a.hom) ≫
                Fiber.fiberInclusion.map e.hom.val =
                  Fiber.fiberInclusion.map φ.inv ≫ b.hom
              rw [Category.assoc, e.hom.property]
              rfl)
          let θ : tangentCongrType φ M b ⟶ tangentCongrType φ M a :=
            UnderLift.homMk e.inv.val (by
              change (Fiber.fiberInclusion.map φ.inv ≫ b.hom) ≫
                Fiber.fiberInclusion.map e.inv.val =
                  Fiber.fiberInclusion.map φ.inv ≫ a.hom
              rw [Category.assoc, e.inv.property]
              rfl)
          exact Quotient.sound ⟨{
            hom := η
            inv := θ
            hom_inv_id := by
              apply Subtype.ext
              exact congrArg (fun f : a ⟶ a ↦ f.val) e.hom_inv_id
            inv_hom_id := by
              apply Subtype.ext
              exact congrArg (fun f : b ⟶ b ↦ f.val) e.inv_hom_id }⟩) (tangentForget x M t) := sorry

end Congruence

end AlgebraicGeometry.GroupoidsOver
