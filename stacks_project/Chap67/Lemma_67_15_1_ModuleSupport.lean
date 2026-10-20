/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support

/-!
# Étale-site support of an 𝒪_X-module

The support of an `𝒪_X`-module on an algebraic space is the set of points of `|X|`
at which an étale module stalk is a nonzero object of `ModuleCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules), Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_iff_moduleStalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (x : Points X),
    x ∈ moduleSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (stalkModuleCat xbar F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport_isZero_iff_of_image_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    (xbar tbar : GeometricPoint X) (himage : xbar.image = tbar.image),
    IsZero (stalkModuleCat xbar F) ↔ IsZero (stalkModuleCat tbar F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_iff_stalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (xbar : GeometricPoint X),
    xbar.image ∈ moduleSupport F ↔ ¬ IsZero (stalkModuleCat xbar F))
