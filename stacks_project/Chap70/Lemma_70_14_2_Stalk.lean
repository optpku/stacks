/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap66.Definition_66_19_6_Stalk
public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Étale module stalks at geometric points

The stalk of an `𝒪_X`-module at a geometric point is the colimit of its étale sections,
after forgetting the abelian-group structure and lifting to universe `u + 1`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The underlying type-valued étale presheaf of a module sheaf, lifted to universe `u + 1`. -/
def typePresheaf (ℱ : X.Modules) : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1) :=
  ℱ.val.presheaf ⋙ forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u + 1, u}

/-- The morphism of type-valued étale presheaves induced by a morphism of module sheaves. -/
def typePresheafMap {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    typePresheaf ℱ ⟶ typePresheaf 𝒢 :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf (structureSheaf X).obj).map f.val)
    (forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u + 1, u})

/-- The stalk of an `𝒪_X`-module at a geometric point, as the colimit of étale sections. -/
def stalk (xbar : GeometricPoint X) (ℱ : X.Modules) : Type (u + 1) :=
  GeometricPoint.stalk xbar (typePresheaf ℱ)

/-- The germ of a module section at a geometric point. -/
def toStalk (xbar : GeometricPoint X) {ℱ : X.Modules}
    (N : GeometricPoint.SmallEtaleNeighborhood xbar)
    (σ : ℱ.val.obj (op N.toSite)) : stalk xbar ℱ :=
  GeometricPoint.toStalk N (ULift.up σ)

/-- The map on geometric-point stalks induced by a morphism of `𝒪_X`-modules. -/
def stalkMap (xbar : GeometricPoint X) {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    stalk xbar ℱ → stalk xbar 𝒢 :=
  (GeometricPoint.stalkFunctor xbar).map (typePresheafMap f)

/-- The germ of a scalar multiple `r • σ`, as the action of a structure-sheaf section on a
module section over an étale neighborhood. -/
def stalkSMul (xbar : GeometricPoint X) {ℱ : X.Modules}
    (N : GeometricPoint.SmallEtaleNeighborhood xbar)
    (r : (structureSheaf X).obj.obj (op N.toSite))
    (σ : ℱ.val.obj (op N.toSite)) : stalk xbar ℱ :=
  toStalk xbar N (r • σ)

end AlgebraicGeometry.AlgebraicSpace.Modules

