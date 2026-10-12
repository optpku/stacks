/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Map
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
public import ReasLib.CategoryTheory.Sites.Chaotic
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of quasi-coherent derived modules on chaotic sites

A functor between categories induces a morphism between their chaotic topoi.  After supplying
the inverse-image structure-ring map, its derived module pullback preserves the canonical
comparison-defined quasi-coherent subcategories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u₀ v₀ u₁ v₁ w

namespace RingedSite.Chaotic

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable (u : C₁ ⥤ C₀)
variable [∀ F : C₁ᵒᵖ ⥤ Type (max u₀ v₀ u₁ v₁ w),
  u.op.HasPointwiseRightKanExtension F]

variable (O : Sheaf (⊥ : GrothendieckTopology C₀)
  CommRingCat.{max u₀ v₀ u₁ v₁ w})
variable (O' : Sheaf (⊥ : GrothendieckTopology C₁)
  CommRingCat.{max u₀ v₀ u₁ v₁ w})

/-- The morphism of topoi induced by a functor between categories equipped with the chaotic
topology.  Its inverse image is restriction along `u`. -/
@[stacks 0GZ1 "underlying morphism of chaotic topoi"]
noncomputable abbrev associatedTopos :=
  u.morphismOfTopoiInOfCocontinuous
    (⊥ : GrothendieckTopology C₁) (⊥ : GrothendieckTopology C₀)

/-- The canonical ring-valued inverse image of `O` along the morphism of chaotic topoi induced
by `u`. -/
@[stacks 0GZ1 "inverse-image structure ring"]
noncomputable abbrev inverseImageRingSheaf :
    Sheaf (⊥ : GrothendieckTopology C₁)
      RingCat.{max u₀ v₀ u₁ v₁ w} :=
  (associatedTopos u).ringInverseImage.obj
    (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₀) O).structureSheaf

/-- The morphism of ringed topoi induced by `u : C₁ ⥤ C₀` and the structure map
`gSharp : g⁻¹O ⟶ O'`. -/
@[stacks 0GZ1 "morphism of chaotic ringed topoi"]
noncomputable abbrev toposHom
    (gSharp : inverseImageRingSheaf u O ⟶
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₁) O').structureSheaf) :
    RingedSite.ToposHom
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₁) O')
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₀) O) where
  toTopos := associatedTopos u
  structureMap := gSharp

set_option synthInstance.maxHeartbeats 100000 in
/-- Existence of the unbounded derived inverse image attached to `toposHom u O O' gSharp`.
This is kept separate from the concrete functor so callers may supply an actual derived-functor
construction without making its data depend on a placeholder proof. -/
@[stacks 0GZ1 "existence of derived inverse image"]
abbrev HasDerivedPullback
    (gSharp : inverseImageRingSheaf u O ⟶
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₁) O').structureSheaf)
    [(SheafOfModules.restrictScalars.{max u₀ v₀ u₁ v₁ w} gSharp).IsRightAdjoint] : Prop :=
  (toposHom u O O' gSharp).HasModulePullbackDerived

set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical unbounded derived inverse image `Lg^*` attached to a morphism of chaotic
ringed topoi. -/
@[stacks 0GZ1 "derived inverse image"]
noncomputable abbrev derivedPullback
    (gSharp : inverseImageRingSheaf u O ⟶
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₁) O').structureSheaf)
    [(SheafOfModules.restrictScalars.{max u₀ v₀ u₁ v₁ w} gSharp).IsRightAdjoint]
    [HasDerivedPullback u O O' gSharp] :
    RingedSite.Hom.ModuleDerived.{max u₀ v₀ u₁ v₁ w}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₀) O) ⥤
      RingedSite.Hom.ModuleDerived.{max u₀ v₀ u₁ v₁ w}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₁) O') :=
  (toposHom u O O' gSharp).modulePullbackDerived

end RingedSite.Chaotic

namespace CategoryTheory.ModulesOnCategory.Chaotic.Pullback

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable (u : C₁ ⥤ C₀)
variable [∀ F : C₁ᵒᵖ ⥤ Type (max u₀ v₀ u₁ v₁ w),
  u.op.HasPointwiseRightKanExtension F]

variable (O : Sheaf (⊥ : GrothendieckTopology C₀)
  CommRingCat.{max u₀ v₀ u₁ v₁ w})
variable (O' : Sheaf (⊥ : GrothendieckTopology C₁)
  CommRingCat.{max u₀ v₀ u₁ v₁ w})
variable (gSharp : RingedSite.Chaotic.inverseImageRingSheaf u O ⟶
  (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₁) O').structureSheaf)
variable [(SheafOfModules.restrictScalars.{max u₀ v₀ u₁ v₁ w} gSharp).IsRightAdjoint]
variable [RingedSite.Chaotic.HasDerivedPullback u O O' gSharp]

/-- Lemma 21.43.10 (0GZ1): derived inverse image along the ringed-topos morphism induced by
`u` and `gSharp` carries canonical quasi-coherent objects on `O` to canonical quasi-coherent
objects on `O'`. -/
@[stacks 0GZ1]
theorem mapsTo :
    isQuasiCoherent.{u₀, v₀, max u₁ v₁ w} O ≤
      (isQuasiCoherent.{u₁, v₁, max u₀ v₀ w} O').inverseImage
      (RingedSite.Chaotic.derivedPullback u O O' gSharp) := sorry

/-- Objectwise form of `mapsTo`: the derived pullback of a canonical quasi-coherent object is
canonical quasi-coherent. -/
theorem obj_mem {K : RingedSite.Hom.ModuleDerived.{max u₀ v₀ u₁ v₁ w}
    (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C₀) O)}
    (hK : isQuasiCoherent.{u₀, v₀, max u₁ v₁ w} O K) :
    isQuasiCoherent.{u₁, v₁, max u₀ v₀ w} O'
      ((RingedSite.Chaotic.derivedPullback u O O' gSharp).obj K) := sorry

/-- Derived inverse image restricted to the canonical quasi-coherent full subcategories. -/
@[stacks 0GZ1 "restricted derived inverse image"]
noncomputable def functor :
    QC.{u₀, v₀, max u₁ v₁ w} O ⥤ QC.{u₁, v₁, max u₀ v₀ w} O' :=
  ObjectProperty.FullSubcategory.restrict
    (RingedSite.Chaotic.derivedPullback u O O' gSharp) (mapsTo u O O' gSharp)

/-- Forgetting the restricted derived inverse image recovers the ambient derived pullback. -/
noncomputable def compιIso :
    functor u O O' gSharp ⋙
        (isQuasiCoherent.{u₁, v₁, max u₀ v₀ w} O').ι ≅
      (isQuasiCoherent.{u₀, v₀, max u₁ v₁ w} O).ι ⋙
        RingedSite.Chaotic.derivedPullback u O O' gSharp :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (RingedSite.Chaotic.derivedPullback u O O' gSharp) (mapsTo u O O' gSharp)

/-- The underlying object of restricted derived pullback is the ambient derived pullback. -/
@[simp]
theorem functor_obj_obj (K : QC.{u₀, v₀, max u₁ v₁ w} O) :
    ((functor u O O' gSharp).obj K).obj =
      (RingedSite.Chaotic.derivedPullback u O O' gSharp).obj K.obj := sorry

end CategoryTheory.ModulesOnCategory.Chaotic.Pullback
