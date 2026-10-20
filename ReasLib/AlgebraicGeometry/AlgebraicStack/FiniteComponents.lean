/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Finite irreducible components on compact opens of algebraic stacks

Finiteness of irreducible components on compact opens can be tested on a smooth
scheme atlas, on all smooth schemes or algebraic spaces, or on the point spaces
of quasi-compact smooth algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every algebraic space smooth over `X` satisfies
`AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens`. -/
def forallSmoothSpaceFiniteComponents {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∀ (Y : AlgebraicSpace S) (p : Y.toGroupoids ⟶ X),
    Groupoids.Hom.Smooth p → AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens Y

/-- `forallSmoothSpaceFiniteComponents X` means every smooth morphism from an algebraic
space to `X` has finitely many irreducible components on compact opens. -/
theorem forallSmoothSpaceFiniteComponents_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    forallSmoothSpaceFiniteComponents X ↔
      ∀ (Y : AlgebraicSpace S) (p : Y.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p →
          AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens Y := sorry

namespace forallSmoothSpaceFiniteComponents

/-- If `forallSmoothSpaceFiniteComponents X`, then every smooth morphism from an
algebraic space `Y` to `X` has finitely many irreducible components on compact
opens. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : forallSmoothSpaceFiniteComponents X) {Y : AlgebraicSpace S}
    (p : Y.toGroupoids ⟶ X) (hp : Groupoids.Hom.Smooth p) :
    AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens Y := sorry

end forallSmoothSpaceFiniteComponents

/-- `forallSmoothSpaceFiniteComponents X` is the smooth algebraic-space atlas form
of the scheme-level finite-components property. -/
theorem forallSmoothSpaceFiniteComponents_iff_forallSmoothSpace {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    forallSmoothSpaceFiniteComponents X ↔
      forallSmoothSpace
        (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X := sorry

/-- Every quasi-compact algebraic stack smooth over `X` has finitely many irreducible
components on its space of points. -/
def finiteIrreducibleComponentsOnSmoothCompact {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∀ {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X),
    IsQuasiCompact Y → Smooth f →
      (irreducibleComponents (Points Y)).Finite

/-- `finiteIrreducibleComponentsOnSmoothCompact X` means every quasi-compact algebraic
stack smooth over `X` has finitely many irreducible components in every canonical
topology on `Points Y`. -/
theorem finiteIrreducibleComponentsOnSmoothCompact_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    finiteIrreducibleComponentsOnSmoothCompact X ↔
      ∀ (Y : GroupoidsOver S) [AlgebraicStack Y] (f : Y ⟶ X),
        IsQuasiCompact Y → Smooth f →
          ∀ (τ : TopologicalSpace (Points Y)),
            IsPointsTopology Y τ → (@irreducibleComponents (Points Y) τ).Finite := sorry

namespace finiteIrreducibleComponentsOnSmoothCompact

/-- If `finiteIrreducibleComponentsOnSmoothCompact X`, then every quasi-compact
algebraic stack smooth over `X` has finitely many irreducible components on its
space of points. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : Y ⟶ X)
    (h : finiteIrreducibleComponentsOnSmoothCompact X)
    (hY : IsQuasiCompact Y) (hf : Smooth f)
    {τ : TopologicalSpace (Points Y)} (hτ : IsPointsTopology Y τ) :
    (@irreducibleComponents (Points Y) τ).Finite := sorry

end finiteIrreducibleComponentsOnSmoothCompact

/-- An algebraic stack has finitely many irreducible components on compact opens if it
admits a surjective smooth scheme atlas whose source has finitely many irreducible
components on every quasi-compact open. -/
@[mk_iff]
class HasFiniteIrreducibleComponentsOnCompactOpens {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth scheme atlas with finitely many irreducible
  components on compact opens. -/
  exists_finiteComponents_smoothCover :
    existsSurjectiveSmooth
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- An algebraic stack with finitely many irreducible components on compact opens
admits a surjective smooth scheme atlas from a scheme with that property. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    existsSurjectiveSmooth
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X := sorry

/-- A surjective smooth scheme atlas from a scheme with finitely many irreducible
components on compact opens witnesses the algebraic-stack property. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsSurjectiveSmooth
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X) :
    HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

/-- An algebraic stack has finitely many irreducible components on compact opens if
and only if every smooth morphism from a scheme has that property on the source. -/
theorem iff_forallSmooth {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔
      forallSmooth
        (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X := sorry

/-- An algebraic stack has finitely many irreducible components on compact opens if
and only if every algebraic space smooth over it has finitely many irreducible
components on compact opens. -/
theorem iff_forallSmoothSpaceFiniteComponents {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔
      forallSmoothSpaceFiniteComponents X := sorry

/-- An algebraic stack has finitely many irreducible components on compact opens if
and only if every quasi-compact algebraic stack smooth over it has finitely many
irreducible components on its space of points. -/
theorem iff_finiteIrreducibleComponentsOnSmoothCompact {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔
      finiteIrreducibleComponentsOnSmoothCompact X := sorry

/-- An algebraic stack has finitely many irreducible components on compact opens if
and only if it has the corresponding smooth-local scheme property. -/
theorem iff_hasSmoothLocal {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔
      hasSmoothLocal
        (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X := sorry

/-- For an algebraic stack, the existence of a surjective smooth scheme atlas with
finitely many irreducible components on compact opens is equivalent to the same
condition for every smooth scheme, the corresponding condition for every smooth
algebraic space, and finiteness of irreducible components of the point space of
every quasi-compact algebraic stack smooth over it. -/
theorem tfae {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    List.TFAE
      [existsSurjectiveSmooth
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallSmooth
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallSmoothSpaceFiniteComponents X,
        finiteIrreducibleComponentsOnSmoothCompact X] := sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

/-- A scheme over `S` with finitely many irreducible components on compact opens,
viewed as an algebraic stack, has that property. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_slice {S : Scheme.{u}}
    (U : Over S) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] :
    HasFiniteIrreducibleComponentsOnCompactOpens (GroupoidsOver.slice U) where
  exists_finiteComponents_smoothCover :=
    existsSurjectiveSmooth.of (𝟙 (GroupoidsOver.slice U)) inferInstance

/-- An algebraic space with finitely many irreducible components on compact opens,
viewed as an algebraic stack, has that property. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_toGroupoids
    {S : Scheme.{u}} (F : AlgebraicSpace S)
    [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens F] :
    HasFiniteIrreducibleComponentsOnCompactOpens F.toGroupoids := sorry

end AlgebraicGeometry.AlgebraicStack
