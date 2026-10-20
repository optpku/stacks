/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic

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


open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace

/-- The small étale site of an algebraic space is locally small in the coefficient universe. -/
instance smallEtaleSite.instLocallySmall {S : Scheme.{u}} (X : AlgebraicSpace S) :
    LocallySmall.{u} (smallEtaleSite X) :=
  sorry

namespace Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The module-valued étale stalk of an `𝒪_X`-module at a geometric point `xbar`, as a module
over `etaleLocalRing X xbar`. The geometric point lies over `xbar.image ∈ |X|`. -/
noncomputable abbrev stalkModuleCat (xbar : GeometricPoint X) (F : X.Modules) :
    ModuleCat (etaleLocalRing X xbar) :=
  ((toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)).obj F

/-- The module-valued étale stalk is the site-point module fiber of `F`. -/
theorem stalkModuleCat_def (xbar : GeometricPoint X) (F : X.Modules) :
    stalkModuleCat xbar F =
      ((toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)).obj F :=
  sorry

/-- The morphism of étale module stalks induced by a morphism of `𝒪_X`-modules. -/
noncomputable def stalkModuleCatMap (xbar : GeometricPoint X) {F G : X.Modules} (f : F ⟶ G) :
    stalkModuleCat xbar F ⟶ stalkModuleCat xbar G :=
  ((toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)).map f

/-- `stalkModuleCatMap` is the module-stalk functor applied to a morphism of sheaves. -/
theorem stalkModuleCatMap_eq (xbar : GeometricPoint X) {F G : X.Modules} (f : F ⟶ G) :
    stalkModuleCatMap xbar f =
      ((toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)).map f :=
  sorry

/-- The identity morphism of modules induces the identity on étale module stalks. -/
theorem stalkModuleCatMap_id (xbar : GeometricPoint X) (F : X.Modules) :
    stalkModuleCatMap xbar (𝟙 F) = 𝟙 (stalkModuleCat xbar F) :=
  sorry

/-- Stalk maps are functorial in morphisms of `𝒪_X`-modules. -/
theorem stalkModuleCatMap_comp (xbar : GeometricPoint X) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    stalkModuleCatMap xbar (f ≫ g) = stalkModuleCatMap xbar f ≫ stalkModuleCatMap xbar g :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
