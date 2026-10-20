/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Module-valued étale stalks of algebraic spaces

The stalk of an `𝒪_X`-module at a geometric point, as a module over the étale local ring
`𝒪_{X, xbar}`, is the site-point module fiber of the small étale ringed site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite.instLocallySmall :
  (X : AlgebraicSpace S) → LocallySmall.{u} (smallEtaleSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCat :
  (xbar : GeometricPoint X) → (F : X.Modules) → ModuleCat (etaleLocalRing X xbar))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCat_def :
  (xbar : GeometricPoint X) → (F : X.Modules) →
    Modules.stalkModuleCat xbar F =
      ((toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)).obj F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCatMap :
  (xbar : GeometricPoint X) → {F G : X.Modules} → (F ⟶ G) →
    (Modules.stalkModuleCat xbar F ⟶ Modules.stalkModuleCat xbar G))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCatMap_eq :
  (xbar : GeometricPoint X) → {F G : X.Modules} → (f : F ⟶ G) →
    Modules.stalkModuleCatMap xbar f =
      ((toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)).map f)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCatMap_id :
  (xbar : GeometricPoint X) → (F : X.Modules) →
    Modules.stalkModuleCatMap xbar (𝟙 F) = 𝟙 (Modules.stalkModuleCat xbar F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCatMap_comp :
  (xbar : GeometricPoint X) → {F G H : X.Modules} → (f : F ⟶ G) → (g : G ⟶ H) →
    Modules.stalkModuleCatMap xbar (f ≫ g) =
      Modules.stalkModuleCatMap xbar f ≫ Modules.stalkModuleCatMap xbar g)
