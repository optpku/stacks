/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure

/-!
# Restriction of coherent modules

This file defines the canonical restriction functor on coherent module sheaves along an open
immersion and records its exactness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace IsCoherent

/-- Restriction along an open immersion preserves coherent module sheaves when the target is
locally Noetherian. -/
theorem restrict {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {F : Y.Modules} (hF : F.IsCoherent) (f : X ⟶ Y) [IsOpenImmersion f] :
    ((restrictFunctor f).obj F).IsCoherent := sorry

end IsCoherent

/-- The canonical functor restricting coherent module sheaves along an open immersion. -/
noncomputable def coherentRestrictFunctor {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    RingedSpace.Coh Y.toRingedSpace ⥤ RingedSpace.Coh X.toRingedSpace :=
  (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).lift
    ((SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).ι ⋙ restrictFunctor f)
    (fun F ↦ AlgebraicGeometry.Scheme.Modules.IsCoherent.restrict F.property f)

/-- The underlying module of a restricted coherent module is its ordinary module restriction. -/
@[simp]
theorem coherentRestrictFunctor_obj_obj {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (F : RingedSpace.Coh Y.toRingedSpace) :
    ((coherentRestrictFunctor f).obj F).obj = (restrictFunctor f).obj F.obj := rfl

/-- The underlying map of a restricted coherent-module morphism is its ordinary restricted map.
-/
@[simp]
theorem coherentRestrictFunctor_map_hom {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f]
    {F G : RingedSpace.Coh Y.toRingedSpace} (g : F ⟶ G) :
    ((coherentRestrictFunctor f).map g).hom = (restrictFunctor f).map g.hom := rfl

/-- Restriction of coherent module sheaves along an open immersion is exact. -/
theorem coherentRestrictFunctor_exact {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    exactFunctor (RingedSpace.Coh Y.toRingedSpace) (RingedSpace.Coh X.toRingedSpace)
      (coherentRestrictFunctor f) := sorry

/-- The canonical coherent-module restriction functor preserves finite limits. -/
instance coherentRestrictFunctor_preservesFiniteLimits
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (coherentRestrictFunctor f) :=
  (coherentRestrictFunctor_exact f).1

/-- The canonical coherent-module restriction functor preserves finite colimits. -/
instance coherentRestrictFunctor_preservesFiniteColimits
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteColimits (coherentRestrictFunctor f) :=
  (coherentRestrictFunctor_exact f).2

end AlgebraicGeometry.Scheme.Modules
