/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.GeometricPoint

/-!
# Étale-stalk length of a module on an algebraic space

The length of a quasi-coherent `𝒪_X`-module at a geometric point is the module length of
its étale stalk. On étale scheme charts this agrees with `lengthOnEtaleChart`, independently
of the chosen geometric point over a given point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- The length of an `𝒪_X`-module at a geometric point `xbar`, as the module length of the
étale stalk `stalkModuleCat xbar F` over `etaleLocalRing X xbar`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthAtGeometricPoint :
  ∀ (F : X.Modules) (xbar : GeometricPoint X), ℕ∞)

/- `lengthAtGeometricPoint F xbar` is the module length of the étale stalk of `F` at `xbar`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthAtGeometricPoint_eq :
  ∀ (F : X.Modules) (xbar : GeometricPoint X),
    lengthAtGeometricPoint F xbar =
      Module.length (etaleLocalRing X xbar) (stalkModuleCat xbar F))

/- For a quasi-coherent module, the étale-stalk length at `xbar` equals the Zariski-stalk
length of `F` on any étale scheme chart whose image point is `xbar.image`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthAtGeometricPoint_eq_lengthOnEtaleChart :
  ∀ (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = xbar.image),
    lengthAtGeometricPoint F xbar = lengthOnEtaleChart φ F u)

/- For a quasi-coherent module, étale-stalk length depends only on the image point of the
geometric point in `|X|`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthAtGeometricPoint_eq_of_liesOver :
  ∀ (F : X.Modules) [F.IsQuasicoherent]
    {xbar ybar : GeometricPoint X} (h : xbar.image = ybar.image),
    lengthAtGeometricPoint F xbar = lengthAtGeometricPoint F ybar)

end AlgebraicGeometry.AlgebraicSpace.Modules
