/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Pullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of ideals on locally ringed spaces

This leaf is the thin locally-ringed-space specialization of inverse-image ideal subobjects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IdealSubobject

/-- The pulled-back ideal map `f^*I ⟶ 𝒪_Y`. -/
@[stacks 01HQ "locally-ringed-space inverse-image ideal map"]
noncomputable abbrev pullbackMap
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :=
  RingedSpace.IdealSubobject.pullbackMap I f.toShHom

/-- The inverse-image ideal subobject along a locally ringed-space morphism. -/
@[stacks 01HQ "inverse-image ideal"]
noncomputable abbrev pullback
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) : IdealSubobject Y :=
  RingedSpace.IdealSubobject.pullback I f.toShHom

/-- The canonical factorization of a pulled-back ideal map through its image ideal. -/
@[stacks 01HQ "locally-ringed-space inverse-image ideal factor"]
noncomputable abbrev pullbackFactor
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    (RingedSpace.Hom.pullback f.toShHom).obj I.toModule ⟶
      (I.pullback f).toModule :=
  RingedSpace.IdealSubobject.pullbackFactor I f.toShHom

/-- The canonical factorization through the inverse-image ideal recovers the pulled-back map. -/
@[reassoc (attr := simp), stacks 01HQ "inverse-image ideal factorization law"]
theorem pullbackFactor_fac
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullbackFactor f ≫ (I.pullback f).arrow = I.pullbackMap f := sorry

/-- The inverse-image ideal is the least ideal through which the pulled-back ideal map factors. -/
@[stacks 01HQ "inverse-image ideal universal property"]
theorem pullback_le_iff
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X)
    (J : IdealSubobject Y) :
    I.pullback f ≤ J ↔
      ∃ g : (RingedSpace.Hom.pullback f.toShHom).obj I.toModule ⟶ J.toModule,
        g ≫ J.arrow = I.pullbackMap f := sorry

/-- Inverse image is monotone on locally-ringed-space ideal subobjects. -/
@[stacks 01HQ "inverse-image ideal monotonicity"]
theorem pullback_mono
    {X Y : LocallyRingedSpace.{u}} {I J : IdealSubobject X} (h : I ≤ J) (f : Y ⟶ X) :
    I.pullback f ≤ J.pullback f := sorry

/-- Pulling an ideal subobject back along the identity leaves it unchanged. -/
@[simp, stacks 01HQ "inverse-image ideal identity"]
theorem pullback_id
    {X : LocallyRingedSpace.{u}} (I : IdealSubobject X) :
    I.pullback (𝟙 X) = I := sorry

/-- Inverse-image ideal subobjects are compatible with composition. -/
@[simp, stacks 01HQ "inverse-image ideal composition"]
theorem pullback_comp
    {X Y Z : LocallyRingedSpace.{u}} (I : IdealSubobject X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    I.pullback (g ≫ f) = (I.pullback f).pullback g := sorry

end AlgebraicGeometry.LocallyRingedSpace.IdealSubobject
