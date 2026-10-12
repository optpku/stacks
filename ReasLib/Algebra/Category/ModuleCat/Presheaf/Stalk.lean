/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Notation
public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.Topology.Sheaves.Ring.Definition

/-!
# Stalks of presheaves of modules

This file provides the module-valued stalk functors and their germ-level API for a ring presheaf
on a topological space.  The commutative-ring specializations reuse the same underlying map and
only supply the changed scalar ring.
-/

@[expose] public section

open CategoryTheory

universe w u

noncomputable section

variable {X Y : TopCat.{w}}

namespace PresheafOfModules

variable {Z : TopCat.{u}} {𝒪 : Z.Presheaf RingCat.{u}}

/-- The stalk of a presheaf of `𝒪`-modules, retaining its canonical module structure over the
stalk ring `𝒪ₓ`. -/
noncomputable abbrev stalkModuleCat
    (ℱ : PresheafOfModules 𝒪) (x : Z) : ModuleCat (𝒪.stalk x) :=
  ModuleCat.of (𝒪.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x)

/-- The underlying additive map on stalks induced by a morphism of presheaves of modules over a
fixed ring presheaf. -/
noncomputable abbrev stalkMapUnderlying
    {ℱ 𝒢 : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) (x : Z) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x →
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf 𝒪).map f)).hom

/-- The underlying stalk map induced by a module-presheaf morphism preserves addition. -/
theorem stalkMapUnderlying_add
    {ℱ 𝒢 : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) (x : Z)
    (m n : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x) :
    stalkMapUnderlying f x (m + n) =
      stalkMapUnderlying f x m + stalkMapUnderlying f x n := sorry

/-- The underlying stalk map induced by a module-presheaf morphism is linear over the stalk
ring. -/
theorem stalkMapUnderlying_smul
    {ℱ 𝒢 : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) (x : Z)
    (r : 𝒪.stalk x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x) :
    stalkMapUnderlying f x (r • m) =
      (r • stalkMapUnderlying f x m :
        TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x) := sorry

/-- The morphism of stalk modules induced by a morphism of presheaves of modules over a fixed
ring presheaf. -/
noncomputable def stalkMap
    {ℱ 𝒢 : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) (x : Z) :
    stalkModuleCat ℱ x ⟶ stalkModuleCat 𝒢 x :=
  ModuleCat.ofHom
    { toFun := stalkMapUnderlying f x
      map_add' := stalkMapUnderlying_add f x
      map_smul' := stalkMapUnderlying_smul f x }

/-- The module-stalk morphism acts by the ordinary additive stalk map. -/
@[simp]
theorem stalkMap_hom_apply
    {ℱ 𝒢 : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) (x : Z)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x) :
    (stalkMap f x).hom m = stalkMapUnderlying f x m := sorry

/-- Taking a module-presheaf morphism to stalk modules sends the germ of a section to the germ of
its sectionwise image. -/
theorem stalkMap_germ
    {ℱ 𝒢 : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢)
    (U : TopologicalSpace.Opens Z) (x : Z) (hx : x ∈ U) (m : ℱ.obj (Opposite.op U)) :
    (stalkMap f x).hom
        (TopCat.Presheaf.germ ℱ.presheaf U x hx m) =
      TopCat.Presheaf.germ 𝒢.presheaf U x hx (f.app (Opposite.op U) m) := sorry

/-- Taking stalk-module maps preserves identity morphisms. -/
theorem stalkMap_id (ℱ : PresheafOfModules 𝒪) (x : Z) :
    stalkMap (𝟙 ℱ) x = 𝟙 (stalkModuleCat ℱ x) := sorry

/-- Taking stalk-module maps preserves composition. -/
theorem stalkMap_comp
    {ℱ 𝒢 ℋ : PresheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ) (x : Z) :
    stalkMap (f ≫ g) x = stalkMap f x ≫ stalkMap g x := sorry

/-- Taking the stalk of a presheaf of modules at `x` is a functor to modules over the stalk ring
`𝒪ₓ`. -/
noncomputable def stalkFunctor
    (𝒪 : Z.Presheaf RingCat.{u}) (x : Z) :
    PresheafOfModules 𝒪 ⥤ ModuleCat (𝒪.stalk x) where
  obj ℱ := stalkModuleCat ℱ x
  map f := stalkMap f x
  map_id ℱ := stalkMap_id ℱ x
  map_comp f g := stalkMap_comp f g x

/-- Taking stalks of module presheaves over a ring presheaf is additive. -/
instance stalkFunctor_additive
    (𝒪 : Z.Presheaf RingCat.{u}) (x : Z) :
    (stalkFunctor 𝒪 x).Additive := sorry

section CommRing

variable {𝒪c : Z.Presheaf CommRingCat.{u}}

/-- The stalk of a module presheaf over the underlying ring presheaf of `𝒪c`, retaining its
canonical module structure over the commutative-ring stalk `𝒪cₓ`. -/
noncomputable abbrev stalkModuleCatOfCommRing
    (ℱ : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c))
    (x : Z) : ModuleCat (𝒪c.stalk x) :=
  ModuleCat.of (𝒪c.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x)

/-- The germ map from a module of sections to the stalk module, bundled as a morphism into
restriction of scalars along the germ map of rings. -/
@[stacks 007K "module-presheaf germ map"]
noncomputable def germToStalk
    (ℱ : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c))
    (x : Z) (U : TopologicalSpace.Opens Z) (hx : x ∈ U) :
    ℱ.obj (Opposite.op U) ⟶
      (ModuleCat.restrictScalars (𝒪c.germ U x hx).hom).obj
        (stalkModuleCatOfCommRing ℱ x) :=
  ModuleCat.semilinearMapAddEquiv (𝒪c.germ U x hx).hom _ _
    { toFun := TopCat.Presheaf.germ ℱ.presheaf U x hx
      map_add' := (TopCat.Presheaf.germ ℱ.presheaf U x hx).hom.map_add
      map_smul' := PresheafOfModules.germ_smul ℱ x U hx }

/-- The bundled module germ map acts by the ordinary presheaf germ map. -/
@[simp]
theorem germToStalk_apply
    (ℱ : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c))
    (x : Z) (U : TopologicalSpace.Opens Z) (hx : x ∈ U)
    (m : ℱ.obj (Opposite.op U)) :
    germToStalk ℱ x U hx m =
      TopCat.Presheaf.germ ℱ.presheaf U x hx m := sorry

/-- The underlying stalk map of a morphism of module presheaves over an underlying
commutative-ring presheaf is linear over the commutative-ring stalk. -/
theorem stalkMapUnderlying_smul_commRing
    {ℱ 𝒢 : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c)}
    (f : ℱ ⟶ 𝒢) (x : Z) (r : 𝒪c.stalk x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x) :
    stalkMapUnderlying f x (r • m) =
      (r • stalkMapUnderlying f x m :
        TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x) := sorry

/-- The morphism of stalk modules over `𝒪cₓ` induced by a morphism of module presheaves over the
underlying ring presheaf of `𝒪c`. -/
noncomputable def stalkMapOfCommRing
    {ℱ 𝒢 : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c)}
    (f : ℱ ⟶ 𝒢) (x : Z) :
    stalkModuleCatOfCommRing ℱ x ⟶ stalkModuleCatOfCommRing 𝒢 x :=
  ModuleCat.ofHom
    { toFun := stalkMapUnderlying f x
      map_add' := stalkMapUnderlying_add f x
      map_smul' := stalkMapUnderlying_smul_commRing f x }

/-- The commutative-ring stalk-module morphism acts by the ordinary additive stalk map. -/
@[simp]
theorem stalkMapOfCommRing_hom_apply
    {ℱ 𝒢 : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c)}
    (f : ℱ ⟶ 𝒢) (x : Z)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x) :
    (stalkMapOfCommRing f x).hom m = stalkMapUnderlying f x m := sorry

/-- The commutative-ring stalk-module map sends the germ of a section to the germ of its
sectionwise image. -/
theorem stalkMapOfCommRing_germ
    {ℱ 𝒢 : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c)}
    (f : ℱ ⟶ 𝒢) (U : TopologicalSpace.Opens Z) (x : Z) (hx : x ∈ U)
    (m : ℱ.obj (Opposite.op U)) :
    (stalkMapOfCommRing f x).hom
        (TopCat.Presheaf.germ ℱ.presheaf U x hx m) =
      TopCat.Presheaf.germ 𝒢.presheaf U x hx (f.app (Opposite.op U) m) := sorry

/-- Taking commutative-ring stalk-module maps preserves identity morphisms. -/
theorem stalkMapOfCommRing_id
    (ℱ : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c)) (x : Z) :
    stalkMapOfCommRing (𝟙 ℱ) x = 𝟙 (stalkModuleCatOfCommRing ℱ x) := sorry

/-- Taking commutative-ring stalk-module maps preserves composition. -/
theorem stalkMapOfCommRing_comp
    {ℱ 𝒢 ℋ : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c)}
    (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ) (x : Z) :
    stalkMapOfCommRing (f ≫ g) x =
      stalkMapOfCommRing f x ≫ stalkMapOfCommRing g x := sorry

/-- Taking stalks at `x` defines a functor from modules over the underlying ring presheaf of
`𝒪c` to modules over the commutative-ring stalk `𝒪cₓ`. -/
noncomputable def stalkFunctorOfCommRing
    (𝒪c : Z.Presheaf CommRingCat.{u}) (x : Z) :
    PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪c) ⥤
      ModuleCat (𝒪c.stalk x) where
  obj ℱ := stalkModuleCatOfCommRing ℱ x
  map f := stalkMapOfCommRing f x
  map_id ℱ := stalkMapOfCommRing_id ℱ x
  map_comp f g := stalkMapOfCommRing_comp f g x

/-- Taking stalks over a commutative-ring presheaf is additive. -/
instance stalkFunctorOfCommRing_additive
    (𝒪c : Z.Presheaf CommRingCat.{u}) (x : Z) :
    (stalkFunctorOfCommRing 𝒪c x).Additive := sorry

end CommRing

end PresheafOfModules


