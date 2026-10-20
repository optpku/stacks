/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Inertia
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.GeometricallyUnibranch

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FunctionFieldExtension

/-- For the normalization in a finite extension of the function field of a normal integral
scheme, unramifiedness, étaleness, and finite étaleness are equivalent. -/
theorem unramified_tfae
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] :
    let ν := (map X L).fromNormalization
    List.TFAE [Unramified ν, Etale ν, IsFinite ν ∧ Etale ν] := sorry

/-- For the canonical normalization morphism attached to a finite function-field extension,
unramifiedness is equivalent to being étale. -/
theorem unramified_iff_etale
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] :
    let ν := (map X L).fromNormalization
    Unramified ν ↔ Etale ν := sorry

/-- For the canonical normalization morphism attached to a finite function-field extension,
unramifiedness is equivalent to finite étaleness. -/
theorem unramified_iff_finiteEtale
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] :
    let ν := (map X L).fromNormalization
    Unramified ν ↔ IsFinite ν ∧ Etale ν := sorry

/-- For the normalization in a finite function-field extension, the global, stalkwise,
henselian, strict-henselian, and fibre-degree criteria for unramifiedness are equivalent. -/
theorem unramified_tfae_local_criteria
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] :
    let ν := (map X L).fromNormalization
    List.TFAE
      [ Unramified ν
      , Etale ν
      , IsFinite ν ∧ Etale ν
      , ∀ x : X, Unramified (pullback.snd ν (X.fromSpecStalk x))
      , ∀ (x : X) (Rh : Type u) [CommRing Rh]
          [Algebra (X.presheaf.stalk x) Rh]
          [IsHenselizationOf (X.presheaf.stalk x) Rh],
          let g : Spec (CommRingCat.of Rh) ⟶ X :=
            Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rh)) ≫
              X.fromSpecStalk x
          Unramified (pullback.snd ν g)
      , ∀ (x : X) (Rsh : Type u) [CommRing Rsh]
          [Algebra (X.presheaf.stalk x) Rsh]
          [IsStrictHenselizationOf (X.presheaf.stalk x) Rsh],
          let g : Spec (CommRingCat.of Rsh) ⟶ X :=
            Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rsh)) ≫
              X.fromSpecStalk x
          Unramified (pullback.snd ν g)
      , ∀ x : X,
          Etale (ν.fiberToSpecResidueField x) ∧
            Module.finrank X.functionField L ≤ ν.fiberDegree x
      ] := sorry

/-- If the finite function-field extension is Galois, unramifiedness is equivalent to trivial
inertia at every point of the normalization. -/
theorem unramified_iff_trivial_inertia
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L] :
    let ν := (map X L).fromNormalization
    Unramified ν ↔ ∀ y : (map X L).normalization, inertia X L y = ⊥ := sorry

end AlgebraicGeometry.Scheme.FunctionFieldExtension
