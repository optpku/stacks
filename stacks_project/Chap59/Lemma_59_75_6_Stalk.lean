/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import stacks_project.Chap59.Definition_59_29_6
public import stacks_project.Chap59.Lemma_59_29_7

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- Geometric stalk of an étale sheaf of `Λ`-modules, as the site-point fiber
in `ModuleCat Λ`. -/
noncomputable def étaleModuleStalk (sbar : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ModuleCat.{u} Λ :=
  (GeometricPoint.toSmallEtalePoint sbar).presheafFiber.obj F.obj

/-- Underlying type of the module stalk, compared with the Type-valued étale
stalk of the forgotten sheaf. -/
noncomputable def étaleModuleStalk_forget (sbar : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))] :
    (CategoryTheory.forget (ModuleCat.{u} Λ)).obj (étaleModuleStalk sbar F) ≃
      Scheme.Etale.stalk sbar
        ((sheafCompose S.smallEtaleTopology
            (CategoryTheory.forget (ModuleCat.{u} Λ))).obj F).obj :=
  (preservesColimitIso (CategoryTheory.forget (ModuleCat.{u} Λ))
      ((CategoryOfElements.π (GeometricPoint.toSmallEtalePoint sbar).fiber).op ⋙
        F.obj)).toEquiv

end AlgebraicGeometry.Scheme

