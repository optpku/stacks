/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of ideal subobjects on ringed spaces

This leaf owns inverse-image ideals and their universal properties.  Preservation of local
generation is isolated in `Pullback.LocalGeneration`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace IdealSubobject

/-- The canonical map from the pullback of an ideal subobject to the source structure sheaf. -/
@[stacks 01HQ "ringed-space inverse-image ideal map"]
noncomputable def pullbackMap
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    (Hom.pullback f).obj I.toModule ⟶
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) :=
  (Hom.pullback f).map I.arrow ≫
    SheafOfModules.pullbackObjUnitToUnit (Hom.toRingCatSheafHom f)

/-- The inverse-image ideal subobject along a morphism of ringed spaces. -/
@[stacks 01HQ "ringed-space inverse-image ideal"]
noncomputable def pullback
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) : IdealSubobject Y :=
  imageSubobject (I.pullbackMap f)

/-- The canonical factorization of the pulled-back ideal map through its image ideal. -/
@[stacks 01HQ "ringed-space inverse-image ideal factor"]
noncomputable abbrev pullbackFactor
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    (Hom.pullback f).obj I.toModule ⟶ (I.pullback f).toModule :=
  factorThruImageSubobject (I.pullbackMap f)

/-- The canonical factorization through the inverse-image ideal recovers the pulled-back ideal
map to the structure sheaf. -/
@[reassoc (attr := simp), stacks 01HQ "inverse-image ideal factorization law"]
theorem pullbackFactor_fac
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullbackFactor f ≫ (I.pullback f).arrow = I.pullbackMap f := sorry

/-- The inverse-image ideal is the least ideal subobject through which the pulled-back ideal map
factors. -/
@[stacks 01HQ "inverse-image ideal universal property"]
theorem pullback_le_iff
    {X Y : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X)
    (J : IdealSubobject Y) :
    I.pullback f ≤ J ↔
      ∃ g : (Hom.pullback f).obj I.toModule ⟶ J.toModule,
        g ≫ J.arrow = I.pullbackMap f := sorry

/-- Inverse image is monotone on ideal subobjects. -/
@[stacks 01HQ "inverse-image ideal monotonicity"]
theorem pullback_mono
    {X Y : RingedSpace.{u}} {I J : IdealSubobject X} (h : I ≤ J) (f : Y ⟶ X) :
    I.pullback f ≤ J.pullback f := sorry

/-- Pulling an ideal subobject back along the identity leaves it unchanged. -/
@[simp, stacks 01HQ "inverse-image ideal identity"]
theorem pullback_id
    {X : RingedSpace.{u}} (I : IdealSubobject X) :
    I.pullback (𝟙 X) = I := sorry

/-- Inverse-image ideal subobjects are compatible with composition. -/
@[simp, stacks 01HQ "inverse-image ideal composition"]
theorem pullback_comp
    {X Y Z : RingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    I.pullback (g ≫ f) = (I.pullback f).pullback g := sorry

end IdealSubobject

end AlgebraicGeometry.RingedSpace
