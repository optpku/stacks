/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
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
