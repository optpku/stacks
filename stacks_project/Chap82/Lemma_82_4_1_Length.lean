module

public import Mathlib.RingTheory.Length
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap82.Lemma_82_4_4_Length

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

/-- The length of an `𝒪_X`-module at a geometric point `xbar`, as the module length of the
étale stalk `stalkModuleCat xbar F` over `etaleLocalRing X xbar`. -/
def lengthAtGeometricPoint (F : X.Modules) (xbar : GeometricPoint X) : ℕ∞ :=
  Module.length (etaleLocalRing X xbar) (stalkModuleCat xbar F)

/-- `lengthAtGeometricPoint F xbar` is the module length of the étale stalk of `F` at `xbar`. -/
theorem lengthAtGeometricPoint_eq (F : X.Modules) (xbar : GeometricPoint X) :
    lengthAtGeometricPoint F xbar =
      Module.length (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  sorry

/-- For a quasi-coherent module, the étale-stalk length at `xbar` equals the Zariski-stalk
length of `F` on any étale scheme chart whose image point is `xbar.image`. -/
theorem lengthAtGeometricPoint_eq_lengthOnEtaleChart (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = xbar.image) :
    lengthAtGeometricPoint F xbar = lengthOnEtaleChart φ F u :=
  sorry

/-- For a quasi-coherent module, étale-stalk length depends only on the image point of the
geometric point in `|X|`. -/
theorem lengthAtGeometricPoint_eq_of_liesOver (F : X.Modules) [F.IsQuasicoherent]
    {xbar ybar : GeometricPoint X} (h : xbar.image = ybar.image) :
    lengthAtGeometricPoint F xbar = lengthAtGeometricPoint F ybar :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
