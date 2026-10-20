/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic

/-!
# Relative tangent spaces and Kähler differentials

This file identifies the derivation model of a relative tangent space with the
linear dual of the Kähler differentials of the induced map on stalks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative tangent space of a scheme morphism at a point is canonically
linearly equivalent over the residue field to the stalk-linear dual of the
Kähler differentials of the induced map on stalks. -/
noncomputable def relativeTangentSpaceLinearDual
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    tangentSpaceAt f x ≃ₗ[X.residueField x]
      (CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.presheaf.stalk x]
        X.residueField x) :=
  -- Local instance justification (defeq pin): pin the target-to-source stalk action to
  -- the explicit algebra map defining `tangentSpaceAt f x`.
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := stalkAlgebra f x
  -- Local instance justification (defeq pin): pin the composite target-stalk action on the
  -- residue field to the composite used by `tangentSpaceAt f x`.
  let _ : Algebra (S.presheaf.stalk (f x)) (X.residueField x) :=
    ((X.residue x).hom.comp (f.stalkMap x).hom).toAlgebra
  -- Local instance justification (defeq pin): identify the composite scalar action required
  -- by the Kähler universal property with the preceding composite algebra map.
  let _ : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
  let e :
      (CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.presheaf.stalk x]
        X.residueField x) ≃ₗ[X.presheaf.stalk x]
          Derivation (S.presheaf.stalk (f x)) (X.presheaf.stalk x) (X.residueField x) :=
    KaehlerDifferential.linearMapEquivDerivation
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
  { toEquiv := e.symm.toEquiv
    map_add' := e.symm.map_add
    map_smul' := sorry }

/-- Evaluating the tangent-space duality equivalence applies the inverse of the
universal Kähler-differential equivalence. -/
theorem relativeTangentSpaceLinearDual_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (v : tangentSpaceAt f x) :
    relativeTangentSpaceLinearDual f x v =
      (-- Local instance justification (defeq pin): use the stalk algebra defining the
       -- derivation model of `tangentSpaceAt f x`.
       let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := stalkAlgebra f x
       -- Local instance justification (defeq pin): use the composite stalk action defining
       -- the derivation model of `tangentSpaceAt f x`.
       let _ : Algebra (S.presheaf.stalk (f x)) (X.residueField x) :=
         ((X.residue x).hom.comp (f.stalkMap x).hom).toAlgebra
       -- Local instance justification (defeq pin): identify the composite scalar action
       -- required by the Kähler universal property.
       let _ : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
           (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
       (KaehlerDifferential.linearMapEquivDerivation
         (S.presheaf.stalk (f x)) (X.presheaf.stalk x)).symm v) := sorry

end AlgebraicGeometry.Scheme.Hom
