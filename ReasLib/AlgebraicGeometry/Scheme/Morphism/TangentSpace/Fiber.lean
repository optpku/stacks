/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic

/-!
# Tangent spaces of scheme-theoretic fibers

This file compares the relative tangent space of a scheme morphism at a point
with the tangent space of its scheme-theoretic fiber at the distinguished point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The tangent space of the scheme-theoretic fiber over `f x` at the point
`f.asFiber x`, modeled by derivations from its fiber stalk to `κ(x)`. -/
abbrev fiberRelativeTangentSpaceAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Type _ :=
  Derivation (Y.residueField (f x)) (fiberStalkAt f x) (X.residueField x)

/-- Linear forms on the fiber-relative Kähler differentials are canonically
fiber-relative tangent vectors. -/
noncomputable def fiberRelativeTangentLinearDualAux
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (CommRingCat.KaehlerDifferential (fiberBaseResidueFieldToStalk f x) →ₗ[fiberStalkAt f x]
      X.residueField x) ≃ₗ[fiberStalkAt f x] fiberRelativeTangentSpaceAt f x :=
  by
    exact
      KaehlerDifferential.linearMapEquivDerivation
        (Y.residueField (f x))
        (fiberStalkAt f x)

/-- The map on Kähler differentials induced by the canonical stalk square at a
distinguished point of a scheme-theoretic fiber. -/
noncomputable def relativeToFiberCotangentMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    let _ : Module (X.presheaf.stalk x)
        (CommRingCat.KaehlerDifferential (fiberBaseResidueFieldToStalk f x)) :=
      Module.compHom _ (sourceStalkToFiberStalk f x).hom
    CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.presheaf.stalk x]
      CommRingCat.KaehlerDifferential (fiberBaseResidueFieldToStalk f x) :=
  let fac := fiberBaseResidueFieldToStalk_fac f x
  ModuleCat.Hom.hom <|
    @CommRingCat.KaehlerDifferential.map
      (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x)
      (Y.residueField (f x))
      (fiberStalkAt f x)
      (f.stalkMap x)
      (fiberBaseResidueFieldToStalk f x)
      (Y.residue (f x))
      (sourceStalkToFiberStalk f x)
      fac

/-- Restriction of fiber-relative linear forms along the source-to-fiber stalk
map is compatible with the `κ(x)`-action. -/
instance fiberCotangentCompatibleSMul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    let _ : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
    let _ : Module (X.presheaf.stalk x)
        (CommRingCat.KaehlerDifferential (fiberBaseResidueFieldToStalk f x)) :=
      Module.compHom _ (sourceStalkToFiberStalk f x).hom
    LinearMap.CompatibleSMul
      (CommRingCat.KaehlerDifferential (fiberBaseResidueFieldToStalk f x)) (X.residueField x)
      (X.presheaf.stalk x) (fiberStalkAt f x) := sorry

/-- The linear map that sends a tangent vector of the distinguished fiber point
to the corresponding relative tangent vector. -/
noncomputable def fiberToRelativeTangentLinearMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    fiberRelativeTangentSpaceAt f x →ₗ[X.residueField x] relativeTangentSpaceAt f x :=
  -- Local instance justification (defeq pin): pin the base-to-source stalk action to
  -- the algebra map used by `relativeTangentSpaceAt f x`.
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  -- Local instance justification (defeq pin): pin the source-stalk action on `κ(x)` to
  -- the residue map used by `relativeTangentSpaceAt f x`.
  let _ : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  -- Local instance justification (defeq pin): pin the composite base-stalk action on `κ(x)`
  -- to the composite in `relativeTangentSpaceAt f x`.
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.residueField x) :=
    ((X.residue x).hom.comp (f.stalkMap x).hom).toAlgebra
  -- Local instance justification (defeq pin): identify the composite scalar action required by
  -- `KaehlerDifferential.linearMapEquivDerivation` with the preceding composite algebra map.
  let _ : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- Local instance justification (defeq pin): restrict the fiber differential's module action
  -- along exactly `sourceStalkToFiberStalk f x`, the map used by `relativeToFiberCotangentMap`.
  let _ : Module (X.presheaf.stalk x)
      (CommRingCat.KaehlerDifferential (fiberBaseResidueFieldToStalk f x)) :=
    Module.compHom _ (sourceStalkToFiberStalk f x).hom
  { toFun := fun D ↦
      KaehlerDifferential.linearMapEquivDerivation
        (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x)
        ((((fiberRelativeTangentLinearDualAux f x).symm D).restrictScalars
          (X.presheaf.stalk x)).comp (relativeToFiberCotangentMap f x))
    map_add' := sorry
    map_smul' := sorry }

/-- The comparison map from the tangent space of the distinguished fiber point
to the relative tangent space is bijective. -/
theorem fiberToRelativeTangentLinearMap_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    Function.Bijective (fiberToRelativeTangentLinearMap f x) := sorry

/-- The relative tangent space of a scheme morphism at a point is canonically
linearly equivalent over `κ(x)` to the tangent space of the scheme-theoretic
fiber at its distinguished point. -/
@[stacks 0BEA]
noncomputable def relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    relativeTangentSpaceAt f x ≃ₗ[X.residueField x] fiberRelativeTangentSpaceAt f x :=
  { toFun := Function.invFun (fiberToRelativeTangentLinearMap f x)
    invFun := fiberToRelativeTangentLinearMap f x
    map_add' := sorry
    map_smul' := sorry
    left_inv := sorry
    right_inv := sorry }

/-- The inverse linear map of the relative-to-fiber tangent-space equivalence is
the explicit fiber-to-relative tangent comparison. -/
theorem relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt_symm_toLinearMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt f x).symm.toLinearMap =
      fiberToRelativeTangentLinearMap f x := sorry

end AlgebraicGeometry.Scheme.Hom
