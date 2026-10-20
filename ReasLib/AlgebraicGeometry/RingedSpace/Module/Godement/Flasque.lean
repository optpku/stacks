/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.Resolution
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.Topology.Sheaf.Flasque

/-!
# Flasque terms in the Godement resolution

Products of skyscraper modules arising from point-indexed stalk modules are flasque after
forgetting to additive sheaves.  Consequently every positive iterate of the Godement step, and
hence every term of the Godement complex, is flasque.  These canonical facts are registered as
instances so downstream arguments do not need proof-local instance reconstruction.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry CategoryTheory.IteratedEndofunctor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Godement

/-- A product of skyscraper modules associated to a point-indexed family is flasque after
forgetting its module structure. -/
@[stacks 0FKS "flasqueness of a product of skyscraper modules"]
noncomputable instance fromDiscrete_isFlasque (X : RingedSpace.{u}) (M : Discrete X) :
    TopCat.Sheaf.IsFlasque
      ((moduleUnderlyingSheaf X).obj ((fromDiscrete X).obj M)) := sorry

/-- One Godement step is flasque after forgetting its module structure. -/
@[stacks 0FKS "flasqueness of one Godement step"]
noncomputable instance step_isFlasque (X : RingedSpace.{u}) (ℱ : X.Modules) :
    TopCat.Sheaf.IsFlasque
      ((moduleUnderlyingSheaf X).obj ((step X).obj ℱ)) := sorry

/-- Every positive iterate of the Godement step is flasque after forgetting module structure. -/
@[stacks 0FKS "flasqueness of iterated Godement steps"]
noncomputable instance positiveIterate_isFlasque
    (X : RingedSpace.{u}) (ℱ : X.Modules) (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((moduleUnderlyingSheaf X).obj (((step X) ⁺⦋n⦌).obj ℱ)) := sorry

/-- Every term of the functorial Godement complex is flasque after forgetting module structure. -/
@[stacks 0FKS "flasqueness of the terms of the Godement complex"]
noncomputable instance complexTerm_isFlasque
    (X : RingedSpace.{u}) (ℱ : X.Modules) (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((moduleUnderlyingSheaf X).obj (((complex X).obj ℱ).X n)) := sorry

end AlgebraicGeometry.RingedSpace.Godement
