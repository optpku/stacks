/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LowerShriek
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos

/-!
# Module inverse image and lower shriek on associated τ-sites

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces, on
each associated `τ`-site, the module inverse image `f^*` landing in
`Mod(X_τ, O_X)` and its left adjoint `f_!`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/-- The identification `f⁻¹ O_Y ≅ O_X` of associated `τ`-structure sheaves along
the cartesian total functor of a 1-morphism. -/
def associatedStructureSheafInverseImageIso_cartesian :
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
        (X.associatedTopology τ) (Y.associatedTopology τ)).obj
      (associatedStructureSheaf Y τ) ≅ associatedStructureSheaf X τ :=
  associatedStructureSheafInverseImageIso f τ

end AlgebraicGeometry.GroupoidsOver
