module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap98.Lemma_98_18_3
public import stacks_project.Chap98.Lemma_98_21_6_Along

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

section Congruence

variable {X : GroupoidsOver S}


/-- Reindexing a fibre isomorphism along `Spec(A[M]) ⟶ Spec(A)`. -/
def trivialDeformationCongr {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    trivialDeformation x M ≅ trivialDeformation x' M where
  hom := Chosen.reindexMap X.p (specOverInl σA M) φ.hom
  inv := Chosen.reindexMap X.p (specOverInl σA M) φ.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `trivialDeformationCongr` reindexes the supplied fibre isomorphism. -/
theorem trivialDeformationCongr_hom {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    (trivialDeformationCongr φ M).hom =
      Chosen.reindexMap X.p (specOverInl σA M) φ.hom := sorry

/-- Transport `Inf` along a fibre isomorphism over `Spec(A)`. -/
def infCongr [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    (infFunctor x).obj M ⟶ (infFunctor x').obj M :=
  ConcreteCategory.ofHom
    { toFun := fun (α : infType x M) ↦
        ⟨(trivialDeformationCongr φ M).symm ≪≫ α.1 ≪≫ trivialDeformationCongr φ M,
          sorry⟩
      map_add' := sorry
      map_smul' := sorry }

/-- `infCongr` conjugates the underlying automorphism by the trivial deformation
of the fibre isomorphism. -/
theorem infCongr_apply [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    (α : infType x M) :
    (infCongr φ M α).1 =
      (trivialDeformationCongr φ M).symm ≪≫ α.1 ≪≫ trivialDeformationCongr φ M :=
  sorry

/-- Precomposition of a lift morphism with a vertical inverse remains a hom-lift of
the coefficient projection. -/
theorem tangentCongrType_isHomLift {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x')
    (M : ModuleCat.{u} A)
    (a : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) :
    X.p.IsHomLift (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M))
      (Fiber.fiberInclusion.map φ.inv ≫ a.hom) := sorry

/-- Transport `T` along a fibre isomorphism by precomposing lifts with the inverse. -/
def tangentCongrType {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    (a : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) :
    liftCat x' (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  ⟨Under.mk (Fiber.fiberInclusion.map φ.inv ≫ a.hom),
    tangentCongrType_isHomLift φ M a⟩

/-- Well-definedness of isomorphism classes of lifts under `tangentCongrType`. -/
theorem tangentCongrType_lifts_wd {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    {a b : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)}
    (h : Nonempty (a ≅ b)) :
    lifts.mk (tangentCongrType φ M a) = lifts.mk (tangentCongrType φ M b) := sorry

/-- The `A`-linear map `T_x(M) ⟶ T_{x'}(M)` induced by a fibre isomorphism. -/
def tangentCongr [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A) :
    (tangentFunctor x).obj M ⟶ (tangentFunctor x').obj M :=
  ConcreteCategory.ofHom
    { toFun t :=
        (tangentForget x' M).symm
          (Quotient.lift (fun a ↦ lifts.mk (tangentCongrType φ M a))
            (fun _ _ h ↦ tangentCongrType_lifts_wd φ M h) (tangentForget x M t))
      map_add' := sorry
      map_smul' := sorry }

/-- `tangentCongr` precomposes the underlying lift with the inverse fibre
isomorphism. -/
theorem tangentCongr_apply [HasStrongRimSchlessinger X]
    {x x' : X.p.Fiber (Over.mk σA)} (φ : x ≅ x') (M : ModuleCat.{u} A)
    (t : (tangentFunctor x).obj M) :
    tangentForget x' M (tangentCongr φ M t) =
      Quotient.lift (fun a ↦ lifts.mk (tangentCongrType φ M a))
        (fun _ _ h ↦ tangentCongrType_lifts_wd φ M h) (tangentForget x M t) := sorry

end Congruence

section FibreProduct

variable {X Y Z : GroupoidsOver S}
variable (p : X ⟶ Y) (q : Z ⟶ Y)
variable [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
variable [HasStrongRimSchlessinger Z]

/-- The projection of the chosen 2-fibre product `X ×_Y Z`. -/
abbrev apexProjection :=
  FiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)

/-- `apexProjection` is the groupoid projection of `TwoFibreProduct.apex p q`. -/
theorem apexProjection_eq :
    apexProjection p q =
      FiberedCategoryOver.Groupoids.p
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) := sorry

/-- The first projection of a fibre object of `X ×_Y Z`. -/
abbrev fstFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    X.p.Fiber (Over.mk σA) :=
  (fiberFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) (Over.mk σA)).obj w

/-- `fstFiber` is the fibre functor of the first projection of the 2-fibre product. -/
theorem fstFiber_eq (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    fstFiber p q w =
      (fiberFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
        (Over.mk σA)).obj w := sorry

/-- The second projection of a fibre object of `X ×_Y Z`. -/
abbrev sndFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    Z.p.Fiber (Over.mk σA) :=
  (fiberFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (Over.mk σA)).obj w

/-- `sndFiber` is the fibre functor of the second projection of the 2-fibre product. -/
theorem sndFiber_eq (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    sndFiber p q w =
      (fiberFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q)
        (Over.mk σA)).obj w := sorry

/-- The image `y = p(x)` of the first projection of `w`. -/
abbrev baseFiber (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    Y.p.Fiber (Over.mk σA) :=
  (fiberFunctor p (Over.mk σA)).obj (fstFiber p q w)

/-- `baseFiber` is `p` applied to `fstFiber`. -/
theorem baseFiber_eq (w : (apexProjection p q).Fiber
    (Over.mk σA)) :
    baseFiber p q w = (fiberFunctor p (Over.mk σA)).obj (fstFiber p q w) := sorry

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
  asIso (reindexCompare p (specOverInl σA M) (fstFiber p q w)) ≪≫
    α.1 ≪≫
    trivialDeformationCongr (comparisonFiber p q w) M ≪≫
    (asIso (reindexCompare q (specOverInl σA M) (sndFiber p q w))).symm

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

/-- The base arrow of the connecting lift, from `Spec(A)` to `Spec(A[M])`. -/
def connectingBase
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    PseudoPullback.baseObj w.1 ⟶ Over.mk (specTrivSqZero σA M) :=
  eqToHom w.2 ≫ specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)

/-- The total morphism of the connecting lift, with components the trivial
deformation arrows of `x` and `z`. -/
def connectingHom
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    w.1 ⟶ (connectingFiber p q w M α).1 :=
  PseudoPullback.Hom.mk (connectingBase p q w M)
    (trivialDeformationLift (fstFiber p q w) M).hom sorry
    (trivialDeformationLift (sndFiber p q w) M).hom sorry ⟨sorry⟩

/-- The connecting lift is a hom-lift of the coefficient projection `A[M] ⟶ A`. -/
theorem connectingHom_isHomLift
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    (apexProjection p q).IsHomLift
      (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M))
      (connectingHom p q w M α) := sorry

/-- The lift of `w` to `A[M]` whose comparison is `p(x') → y' -α→ y' → q(z')`. -/
def connectingObj
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) (α : infType (baseFiber p q w) M) :
    liftCat w (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  ⟨Under.mk (connectingHom p q w M α), connectingHom_isHomLift p q w M α⟩

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
      ((tangentFunctor w).obj M : Type (u + 1)) :=
  { toFun α := (tangentForget w M).symm (lifts.mk (connectingObj p q w M α))
    map_add' := sorry
    map_smul' := sorry }

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
        asIso (reindexCompare p (specOverInl σA M) (fstFiber p q w)) ≪≫
          α.1 ≪≫ trivialDeformationCongr (comparisonFiber p q w) M ≪≫
          (asIso (reindexCompare q (specOverInl σA M) (sndFiber p q w))).symm := sorry

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

end AlgebraicGeometry.GroupoidsOver
