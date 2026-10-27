/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.Smooth

/-!
# Openness of versality

A category fibred in groupoids over a locally Noetherian scheme satisfies
openness of versality when versality at a finite type point spreads to an open
neighbourhood of finite type points. A 1-morphism satisfies the same axiom
when every slice 2-fibre product does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- A category `X` fibred in groupoids over `(Sch/S)_fppf` satisfies openness of
versality when versality of an object `x` over a locally finite type scheme `U`
at a finite type point `u0` spreads to every finite type point of some open
neighbourhood of `u0`. -/
class OpennessOfVersality {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S) : Prop where
  /-- Versality at a finite type point spreads to an open neighbourhood. -/
  exists_nhd :
    ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
      (hx : X.p.obj x = Over.mk hU) (u0 : U), IsFiniteTypePoint u0 →
      IsVersalAt hU x hx u0 →
        ∃ U' : Opens U, u0 ∈ U' ∧
          ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u

private theorem fullyFaithful_isCartesian
    {C D : Type*} [Category C] [Category D] (p : C ⥤ D) (hp : p.FullyFaithful)
    {R S : D} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [p.IsHomLift f φ] :
    p.IsCartesian f φ := by
  subst_hom_lift p f φ
  clear a b R S
  constructor
  intro a' φ' hφ'
  have ha := IsHomLift.domain_eq p (p.map φ) φ'
  let χ : a' ⟶ a := hp.preimage (eqToHom ha)
  have hχ : p.IsHomLift (𝟙 (p.obj a)) χ := by
    apply IsHomLift.of_fac' p _ _ ha rfl
    simp [χ]
  refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
  · show χ ≫ φ = φ'
    apply hp.map_injective
    simp only [p.map_comp, χ, hp.map_preimage]
    simpa using (IsHomLift.fac' p (p.map φ) φ').symm
  · change ∀ ψ, p.IsHomLift (𝟙 (p.obj a)) ψ ∧ ψ ≫ φ = φ' → ψ = χ
    intro ψ hψ
    letI := hψ.1
    apply hp.map_injective
    simpa [χ] using IsHomLift.fac' p (𝟙 (p.obj a)) ψ

private theorem iteratedSliceForward_inGroupoids
    {C : Type*} [Category C] {S : C} (V : Over S) :
    Functor.IsFibered.InGroupoids (Over.iteratedSliceForward V) := by
  let F := Over.iteratedSliceForward V
  let hF : F.FullyFaithful := (Over.iteratedSliceEquiv V).fullyFaithfulFunctor
  change Functor.IsFibered.InGroupoids F
  refine { exists_isCartesian' := ?_, comp := ?_, all_isCartesian := ?_ }
  · intro a R f
    let b := (Over.iteratedSliceBackward V).obj R
    let φ : b ⟶ a := hF.preimage f
    have hφ : F.IsHomLift f φ := by
      apply IsHomLift.of_fac' F _ _ rfl rfl
      simpa [φ] using hF.map_preimage f
    exact ⟨b, φ, fullyFaithful_isCartesian F hF f φ⟩
  · intro R S T f g a b c φ ψ hφ hψ
    exact fullyFaithful_isCartesian F hF (f ≫ g) (φ ≫ ψ)
  · intro a b φ
    exact fullyFaithful_isCartesian F hF (F.map φ) φ

/-- The 2-fibre product `(Sch/U)_fppf ×_Y X` associated to a 1-morphism
`f : X ⟶ Y` and an object `y` of `Y` over `U`, reindexed as a category fibred
in groupoids over `Over U`. -/
def fiberProductSlice {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) : GroupoidsOver U :=
  ⟨BasedCategory.ofFunctor
    ((FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).p ⋙
      Over.iteratedSliceForward (Over.mk hU)), by
    letI := iteratedSliceForward_inGroupoids (Over.mk hU)
    exact Functor.IsFibered.InGroupoids.Comp.inGroupoids
      (FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).p
      (Over.iteratedSliceForward (Over.mk hU))⟩

/-- The total category of `fiberProductSlice f hU y hy` is the total category of
the slice base change along the 2-Yoneda 1-morphism of `y`. -/
theorem fiberProductSlice_total {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) :
    (fiberProductSlice f hU y hy).total =
      (FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).total :=
  rfl

/-- `fiberProductSlice` is the slice base change of `f` along the 2-Yoneda
1-morphism of `y`, reindexed along `Over.iteratedSliceForward`. -/
theorem fiberProductSlice_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) :
    (fiberProductSlice f hU y hy).toBasedCategory =
      BasedCategory.ofFunctor
        ((FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).p ⋙
          Over.iteratedSliceForward (Over.mk hU)) :=
  rfl

namespace OpennessOfVersality

/-- The canonical slice fibration of a scheme locally of finite type over a
locally Noetherian base satisfies openness of versality. -/
instance slice {S : Scheme.{u}} [IsLocallyNoetherian S] (V : Over S)
    [LocallyOfFiniteType V.hom] :
    OpennessOfVersality (GroupoidsOver.slice V) := by
  constructor
  intro U hU h_lft x hx u0 hu0 hvers
  obtain ⟨T, g, rfl⟩ := CostructuredArrow.mk_surjective x
  change T = Over.mk hU at hx
  subst T
  let f : U ⟶ V.left := g.left
  have h_over : f ≫ V.hom = hU := Over.w g
  have versal_iff (u : U) (hu : IsFiniteTypePoint u) :
      f.SmoothAt u ↔ IsVersalAt (X := GroupoidsOver.slice V) hU (Over.mk g) rfl u := by
    letI := hu
    exact smoothAt_iff_isVersalAt hU V.hom f h_over u
  obtain ⟨W, A, hu0A, e, h_smooth⟩ := (versal_iff u0 hu0).mpr hvers
  refine ⟨(A : Opens U), hu0A, ?_⟩
  intro u hu hu_ft
  apply (versal_iff u hu_ft).mp
  exact ⟨W, A, hu, e, h_smooth⟩

/-- Openness of versality supplies an open neighbourhood of finite type points
on which versality persists. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [OpennessOfVersality X] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) (hu0 : IsFiniteTypePoint u0) (hvers : IsVersalAt hU x hx u0) :
    ∃ U' : Opens U, u0 ∈ U' ∧
      ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  OpennessOfVersality.exists_nhd hU x hx u0 hu0 hvers

/-- Openness of versality is the neighbourhood spreading of versality at finite
type points. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S) :
    OpennessOfVersality X ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
        (hx : X.p.obj x = Over.mk hU) (u0 : U), IsFiniteTypePoint u0 →
        IsVersalAt hU x hx u0 →
          ∃ U' : Opens U, u0 ∈ U' ∧
            ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  ⟨fun h ↦ h.exists_nhd, fun h ↦ ⟨h⟩⟩

end OpennessOfVersality

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.Groupoids.Hom

open AlgebraicGeometry.GroupoidsOver

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` satisfies openness of versality when every slice 2-fibre product
`(Sch/U)_fppf ×_Y X` does. -/
class OpennessOfVersality {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- Every slice 2-fibre product satisfies openness of versality. -/
  ofBaseChange :
    ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
      [IsLocallyNoetherian U] (y : Y.total) (hy : Y.p.obj y = Over.mk hU),
      GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy)

namespace OpennessOfVersality

/-- The identity 1-morphism of a category fibred in groupoids satisfies openness
of versality. -/
instance id {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} :
    OpennessOfVersality (𝟙 X) :=
  sorry

/-- Openness of versality of `f` means every slice 2-fibre product satisfies
openness of versality. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [OpennessOfVersality f] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] [IsLocallyNoetherian U] (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) :
    GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy) :=
  OpennessOfVersality.ofBaseChange hU y hy

/-- Openness of versality of a 1-morphism is openness of versality of every
slice 2-fibre product. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    OpennessOfVersality f ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
        [IsLocallyNoetherian U] (y : Y.total) (hy : Y.p.obj y = Over.mk hU),
        GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy) :=
  ⟨fun h ↦ h.ofBaseChange, fun h ↦ ⟨h⟩⟩

end OpennessOfVersality

end AlgebraicGeometry.Groupoids.Hom
