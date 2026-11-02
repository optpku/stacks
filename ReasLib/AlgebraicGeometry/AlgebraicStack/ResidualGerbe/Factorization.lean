/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Lifting
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.ClosedImmersion.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.Factorization

/-!
# Factorization through residual gerbes

A morphism of algebraic stacks from a reduced source whose image on points is contained in the
singleton `{x}` factors through a residual gerbe at `x` when the target is
decent or locally Noetherian and its inertia morphism is quasi-compact.
For a locally Noetherian target and a closed point `x`, the factorization holds
without quasi-compactness of inertia.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through any residual-gerbe inclusion at `x`, provided the target
is decent or locally Noetherian and its canonical inertia projection is
quasi-compact. -/
@[stacks 0H25]
theorem factorsThrough_of_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι := sorry

/-- If `X` is decent, a morphism from a reduced algebraic stack whose image on
points is contained in `{x}` factors through a residual gerbe at `x`, provided
the inertia morphism of `X` is quasi-compact. -/
theorem factorsThrough_of_isDecent {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsDecent X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι :=
  factorsThrough_of_range_subset_singleton (Or.inl inferInstance) ι f h_image

/-- If `X` is locally Noetherian, a morphism from a reduced algebraic stack whose
image on points is contained in `{x}` factors through a residual gerbe at `x`,
provided the inertia morphism of `X` is quasi-compact. -/
theorem factorsThrough_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι :=
  factorsThrough_of_range_subset_singleton (Or.inr inferInstance) ι f h_image

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through the canonical residual-gerbe inclusion of `X` at `x`,
provided `X` is decent or locally Noetherian and its canonical inertia projection
is quasi-compact. -/
theorem factorsThrough_residualGerbeι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X}
    (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f (residualGerbeι X x) :=
  factorsThrough_of_range_subset_singleton hX (residualGerbeι X x) f h_image

/-- Factoring through a residual gerbe forces the image on points to lie in the
marked singleton, with no reducedness or finiteness hypotheses. -/
theorem range_subset_singleton_of_factorsThrough {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x]
    (f : Y ⟶ X) (hf : FactorsThrough f ι) :
    Set.range (Points.map f) ⊆ {x} := by
  obtain ⟨g, ⟨e⟩⟩ := hf
  rintro _ ⟨y, rfl⟩
  induction y using Quotient.inductionOn with
  | h p =>
    have hy := Points.mem_range_map_of_iso p.structureHom (p.hom ≫ f)
      (p.hom ≫ g) ⟨(α_ p.hom g ι) ≪≫ Bicategory.whiskerLeftIso p.hom e⟩
    rw [IsResidualGerbe.image_eq (ι := ι) (x := x)] at hy
    exact hy

/-- A morphism from a reduced algebraic stack factors through a residual gerbe
at `x` if and only if its image on points is contained in `{x}`, provided `X`
is decent or locally Noetherian and `I_X ⟶ X` is quasi-compact. -/
theorem factorsThrough_iff_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X) :
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x} :=
  ⟨range_subset_singleton_of_factorsThrough ι f,
    factorsThrough_of_range_subset_singleton hX ι f⟩

/-- Factorizations through a residual-gerbe monomorphism are unique up to
2-isomorphism. -/
theorem lift_unique {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] {x : Points X}
    (ι : Z ⟶ X) [IsResidualGerbe ι x] {f : Y ⟶ X} {g g' : Y ⟶ Z}
    (hg : g ≫ ι ≅ f) (hg' : g' ≫ ι ≅ f) :
    Nonempty (g ≅ g') := by
  letI : Groupoids.Hom.Mono ι := IsResidualGerbe.mono (ι := ι) (x := x)
  obtain ⟨hι⟩ := Groupoids.Hom.Mono.fullyFaithful ι
  letI := hι.full
  letI := hι.faithful
  let e := FiberedCategoryOver.Groupoids.toBasedFunctorIso (hg ≪≫ hg'.symm)
  let e' := (BasedNatTrans.forgetful _ _).mapIso e
  let t := Functor.fullyFaithfulCancelRight (FiberedCategoryOver.Groupoids.toFunctor ι) e'
  refine ⟨FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
    (BasedNatIso.mkNatIso t ?_)⟩
  intro y
  apply (BasedFunctor.isHomLift_iff
    (FiberedCategoryOver.Groupoids.toBasedFunctor ι) _ _).mp
  change Functor.IsHomLift _ _
    ((FiberedCategoryOver.Groupoids.toFunctor ι).map
      ((FiberedCategoryOver.Groupoids.toFunctor ι).preimage (e'.hom.app y)))
  rw [Functor.map_preimage]
  exact e.hom.isHomLift' y

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through any residual-gerbe inclusion at a closed point `x` of a
locally Noetherian algebraic stack, without a quasi-compactness assumption on
inertia. -/
@[stacks 0H26]
theorem factorsThrough_of_mem_closedPoints {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι := by
  letI : ClosedImmersion ι := (mem_closedPoints_iff_closedImmersion ι).mp hx
  apply (ClosedImmersion.factorsThrough_iff_range_subset ι f).mpr
  simpa only [IsResidualGerbe.image_eq (ι := ι) (x := x)] using h_image

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through the canonical residual-gerbe inclusion of `X` at a
closed point `x`, when `X` is locally Noetherian. -/
theorem factorsThrough_residualGerbeι_of_mem_closedPoints {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [IsReduced Y] [IsLocallyNoetherian X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f (residualGerbeι X x) :=
  factorsThrough_of_mem_closedPoints hx (residualGerbeι X x) f h_image

/-- A morphism from a reduced algebraic stack factors through a residual gerbe
at a closed point `x` if and only if its image on points is contained in `{x}`,
when `X` is locally Noetherian. -/
theorem factorsThrough_iff_range_subset_singleton_of_mem_closedPoints
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [IsLocallyNoetherian X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) (ι : Z ⟶ X) [IsResidualGerbe ι x]
    (f : Y ⟶ X) :
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x} :=
  ⟨range_subset_singleton_of_factorsThrough ι f,
    factorsThrough_of_mem_closedPoints hx ι f⟩

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
