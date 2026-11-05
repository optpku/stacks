/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Morphism

/-!
# Six-term Inf/T sequence of a 2-fibre product

The five A-linear maps of the exact sequence
`0 → Inf_w(M) → Inf_x(M) × Inf_z(M) → Inf_y(M) → T_w(M) → T_x(M) × T_z(M) → T_y(M)`
at a fibre object of `X ×_Y Z`, including the connecting map that inserts an
infinitesimal automorphism of `y` into the 2-fibre-product comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open CategoryTheory.BasedCategory
open FiberedCategoryOver.Groupoids (fiberFunctor reindexCompare toBasedFunctor)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {A : CommRingCat.{u}} {σA : Spec A ⟶ S}

section FibreProduct

variable {X Y Z : GroupoidsOver S}
variable (p : X ⟶ Y) (q : Z ⟶ Y)
variable [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
variable [HasStrongRimSchlessinger Z]

/-- The projection of the chosen 2-fibre product `X ×_Y Z`. -/
abbrev apexProjection :=
  FiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)

/-- The first projection of a fibre object of `X ×_Y Z`. -/
abbrev fstFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    X.p.Fiber (Over.mk σA) :=
  (fiberFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) (Over.mk σA)).obj w

/-- The second projection of a fibre object of `X ×_Y Z`. -/
abbrev sndFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    Z.p.Fiber (Over.mk σA) :=
  (fiberFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (Over.mk σA)).obj w

/-- The image `y = p(x)` of the first projection of `w`. -/
abbrev baseFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    Y.p.Fiber (Over.mk σA) :=
  (fiberFunctor p (Over.mk σA)).obj (fstFiber p q w)

/-- The 2-fibre-product comparison `p(x) ≅ q(z)` in the fibre over `Spec(A)`. -/
def comparisonFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    baseFiber p q w ≅ (fiberFunctor q (Over.mk σA)).obj (sndFiber p q w) :=
  Fiber.isoMk (PseudoPullback.comparisonIsoApp w.1) sorry

/-- The underlying total morphism of `comparisonFiber` is the stored comparison of
the 2-fibre-product object. -/
theorem comparisonFiber_hom (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    Fiber.fiberInclusion.map (comparisonFiber p q w).hom =
      (PseudoPullback.comparisonIsoApp w.1).hom := sorry

/-- The comparison `p(x') ≅ q(z')` of trivial deformations, with an infinitesimal
automorphism of `y` inserted in the middle. -/
def connectingComparison
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    (fiberFunctor p (Over.mk (specTrivSqZero σA M))).obj
        (trivialDeformation (fstFiber p q w) M) ≅
      (fiberFunctor q (Over.mk (specTrivSqZero σA M))).obj
        (trivialDeformation (sndFiber p q w) M) :=
  reindexCompareIso p (fstFiber p q w) M ≪≫
    α.1 ≪≫
    trivialDeformationCongr (comparisonFiber p q w) M ≪≫
    (reindexCompareIso q (sndFiber p q w) M).symm

/-- The fibre object of `X ×_Y Z` over `Spec(A[M])` with legs the trivial
deformations of `x` and `z` and comparison `p(x') → y' -α→ y' → q(z')`. -/
def connectingFiber
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    (apexProjection p q).Fiber
      (Over.mk (specTrivSqZero σA M)) :=
  ⟨PseudoPullback.mk (toBasedFunctor p) (toBasedFunctor q)
      (Over.mk (specTrivSqZero σA M))
      ⟨trivialDeformation (fstFiber p q w) M,
        trivialDeformation (sndFiber p q w) M,
        connectingComparison p q w M α⟩, rfl⟩

/-- The total morphism of the connecting lift, with components the trivial
deformation arrows of `x` and `z`. -/
def connectingHom
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    w.1 ⟶ (connectingFiber p q w M α).1 := by
  let base := eqToHom w.2 ≫
    specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)
  let fst := (trivialDeformationLift (fstFiber p q w) M).hom
  let snd := (trivialDeformationLift (sndFiber p q w) M).hom
  have laws : X.p.IsHomLift base fst ∧ Z.p.IsHomLift base snd ∧
      CommSq ((toBasedFunctor p).toFunctor.map fst)
        (PseudoPullback.comparison w.1)
        (PseudoPullback.comparison (connectingFiber p q w M α).1)
        ((toBasedFunctor q).toFunctor.map snd) := by sorry
  exact PseudoPullback.Hom.mk base fst laws.1 snd laws.2.1 laws.2.2

/-- The lift of `w` to `A[M]` whose comparison is `p(x') → y' -α→ y' → q(z')`. -/
def connectingObj
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    liftCat w (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  ⟨Under.mk (connectingHom p q w M α), by sorry⟩

/-- The first nonzero map `Inf_w(M) ⟶ Inf_x(M) × Inf_z(M)` of the six-term sequence. -/
def infProd
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    ((infFunctor w).obj M : Type u) →ₗ[A]
      ((infFunctor (fstFiber p q w)).obj M : Type u) ×
        ((infFunctor (sndFiber p q w)).obj M : Type u) :=
  LinearMap.prod
    (infAlong (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w M).hom
    (infAlong (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w M).hom

/-- `infProd` is the pair of infinitesimal maps of the two projections. -/
theorem infProd_apply
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : (infFunctor w).obj M) :
    infProd p q w M α =
      (infAlong (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w M α,
        infAlong (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w M α) := sorry

/-- The difference map `Inf_x(M) × Inf_z(M) ⟶ Inf_y(M)`, sending `(β, γ)` to
`Inf(p)(β) - Inf(q)(γ)` after identifying `Inf_{q(z)}` with `Inf_y`. -/
def infDiff
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    ((infFunctor (fstFiber p q w)).obj M : Type u) ×
        ((infFunctor (sndFiber p q w)).obj M : Type u) →ₗ[A]
      ((infFunctor (baseFiber p q w)).obj M : Type u) :=
  LinearMap.coprod
    (infAlong p (fstFiber p q w) M).hom
    (-((infCongr (comparisonFiber p q w).symm M).hom ∘ₗ
        (infAlong q (sndFiber p q w) M).hom))

/-- `infDiff` evaluates as `Inf(p)(β) - Inf(q)(γ)`. -/
theorem infDiff_apply
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A)
    (β : (infFunctor (fstFiber p q w)).obj M)
    (γ : (infFunctor (sndFiber p q w)).obj M) :
    infDiff p q w M (β, γ) =
      infAlong p (fstFiber p q w) M β -
        infCongr (comparisonFiber p q w).symm M
          (infAlong q (sndFiber p q w) M γ) := sorry

/-- The connecting map `Inf_y(M) ⟶ T_w(M)` sending an infinitesimal automorphism
of the trivial deformation of `y` to the class of `connectingObj`. -/
def connecting
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    ((infFunctor (baseFiber p q w)).obj M : Type u) →ₗ[A]
      ((tangentFunctor w).obj M : Type (u + 1)) := by
  let f : (infFunctor (baseFiber p q w)).obj M → (tangentFunctor w).obj M :=
    fun α ↦ (tangentForget w M).symm (lifts.mk (connectingObj p q w M α))
  have laws : (∀ a b, f (a + b) = f a + f b) ∧
      (∀ (r : A) a, f (r • a) = r • f a) := by sorry
  exact { toFun := f, map_add' := laws.1, map_smul' := laws.2 }

/-- `connecting` is the class of `connectingObj` after identifying `T_w(M)` with
`Lift(w, A[M])`. -/
theorem connecting_apply
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : (infFunctor (baseFiber p q w)).obj M) :
    connecting p q w M α =
      (tangentForget w M).symm (lifts.mk (connectingObj p q w M α)) := sorry

/-- The connecting lift has legs the trivial deformations of `x` and `z`, and its
comparison inserts `α` between `p(x') → y'` and `y' → q(z')`. -/
theorem connecting_spec
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : (infFunctor (baseFiber p q w)).obj M) :
    tangentForget w M (connecting p q w M α) =
        lifts.mk (connectingObj p q w M α) ∧
      PseudoPullback.fstObj (connectingFiber p q w M α).1 =
          (trivialDeformation (fstFiber p q w) M).1 ∧
      PseudoPullback.sndObj (connectingFiber p q w M α).1 =
          (trivialDeformation (sndFiber p q w) M).1 ∧
      connectingComparison p q w M α =
        reindexCompareIso p (fstFiber p q w) M ≪≫
          α.1 ≪≫ trivialDeformationCongr (comparisonFiber p q w) M ≪≫
          (reindexCompareIso q (sndFiber p q w) M).symm := sorry

/-- The differential `T_w(M) ⟶ T_x(M) × T_z(M)` of the two projections. -/
def tangentProd
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    ((tangentFunctor w).obj M : Type (u + 1)) →ₗ[A]
      ((tangentFunctor (fstFiber p q w)).obj M : Type (u + 1)) ×
        ((tangentFunctor (sndFiber p q w)).obj M : Type (u + 1)) :=
  LinearMap.prod
    (tangentAlong (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w M).hom
    (tangentAlong (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w M).hom

/-- `tangentProd` is the pair of tangent maps of the two projections. -/
theorem tangentProd_apply
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (t : (tangentFunctor w).obj M) :
    tangentProd p q w M t =
      (tangentAlong (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w M t,
        tangentAlong (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w M t) := sorry

/-- The difference of differentials `T_x(M) × T_z(M) ⟶ T_y(M)`, sending `(ξ, η)`
to `T(p)(ξ) - T(q)(η)` after identifying `T_{q(z)}` with `T_y`. -/
def tangentDiff
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    ((tangentFunctor (fstFiber p q w)).obj M : Type (u + 1)) ×
        ((tangentFunctor (sndFiber p q w)).obj M : Type (u + 1)) →ₗ[A]
      ((tangentFunctor (baseFiber p q w)).obj M : Type (u + 1)) :=
  LinearMap.coprod
    (tangentAlong p (fstFiber p q w) M).hom
    (-((tangentCongr (comparisonFiber p q w).symm M).hom ∘ₗ
        (tangentAlong q (sndFiber p q w) M).hom))

/-- `tangentDiff` evaluates as `T(p)(ξ) - T(q)(η)`. -/
theorem tangentDiff_apply
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A)
    (ξ : (tangentFunctor (fstFiber p q w)).obj M)
    (η : (tangentFunctor (sndFiber p q w)).obj M) :
    tangentDiff p q w M (ξ, η) =
      tangentAlong p (fstFiber p q w) M ξ -
        tangentCongr (comparisonFiber p q w).symm M
          (tangentAlong q (sndFiber p q w) M η) := sorry

/-- The first nonzero map of the six-term sequence is injective. -/
theorem infProd_injective
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Injective (infProd p q w M) := sorry

/-- Exactness of the six-term sequence at `Inf_x(M) × Inf_z(M)`. -/
theorem exact_infProd_infDiff
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Exact (infProd p q w M) (infDiff p q w M) := sorry

/-- Exactness of the six-term sequence at `Inf_y(M)`. -/
theorem exact_infDiff_connecting
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Exact (infDiff p q w M) (connecting p q w M) := sorry

/-- Exactness of the six-term sequence at `T_w(M)`. -/
theorem exact_connecting_tangentProd
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Exact (connecting p q w M) (tangentProd p q w M) := sorry

/-- Exactness of the six-term sequence at `T_x(M) × T_z(M)`. -/
theorem exact_tangentProd_tangentDiff
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Exact (tangentProd p q w M) (tangentDiff p q w M) := sorry

end FibreProduct

/-- Let `S` be a scheme. Let `p : X ⟶ Y` and `q : Z ⟶ Y` be
1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`. Assume `X`,
`Y`, `Z` satisfy (RS*). Let `A` be an `S`-algebra and let `w` be an object of
`W = X ×_Y Z` over `A`. Denote `x`, `y`, `z` the objects of `X`, `Y`, `Z`
obtained from `w`. For any `A`-module `M` the sequence
`0 ⟶ Inf_w(M) ⟶ Inf_x(M) × Inf_z(M) ⟶ Inf_y(M) ⟶ T_w(M) ⟶ T_x(M) × T_z(M) ⟶ T_y(M)`
of `A`-modules is exact. Horizontal maps come from 1-morphism functoriality of
`Inf` and `T`; the connecting map `Inf_y(M) ⟶ T_w(M)` inserts an infinitesimal
automorphism of the trivial deformation of `y` into the 2-fibre-product
comparison of the trivial deformations of `x` and `z`. -/
@[stacks 0DNN]
theorem infTangentSequence_exact {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
    [HasStrongRimSchlessinger Z] {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Injective (infProd p q w M) ∧
      Function.Exact (infProd p q w M) (infDiff p q w M) ∧
      Function.Exact (infDiff p q w M) (connecting p q w M) ∧
      Function.Exact (connecting p q w M) (tangentProd p q w M) ∧
      Function.Exact (tangentProd p q w M) (tangentDiff p q w M) := sorry

end AlgebraicGeometry.GroupoidsOver
