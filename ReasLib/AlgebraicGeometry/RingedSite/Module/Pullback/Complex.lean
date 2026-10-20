/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of complexes of modules on ringed sites

The inverse-image functor of a bundled morphism of ringed sites acts degreewise on homological
complexes.  This is pure functorial data: it is independent of flatness, K-flatness, and any
commutative presentation of the structure sheaves.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

namespace RingedSite.Hom

/-- Module pullback applied degreewise to unbounded cochain complexes. -/
@[stacks 0G7E "complex pullback"]
noncomputable abbrev modulePullbackComplex.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    CochainComplex (ModuleCat.{z} Y) ℤ ⥤ CochainComplex (ModuleCat.{z} X) ℤ :=
  (f.modulePullback.{z}).mapHomologicalComplex (up ℤ)

/-- Module pullback on the homotopy category of unbounded cochain complexes. -/
@[stacks 0G7E "homotopy-category pullback"]
noncomputable abbrev modulePullbackHomotopy.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    HomotopyCategory (ModuleCat.{z} Y) (up ℤ) ⥤
      HomotopyCategory (ModuleCat.{z} X) (up ℤ) :=
  (f.modulePullback.{z}).mapHomotopyCategory (up ℤ)

namespace modulePullbackComplex

/-- In each degree, complex pullback is the underlying module pullback. -/
@[simp]
theorem obj_X.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (K : CochainComplex (ModuleCat.{z} Y) ℤ) (n : ℤ) :
    ((f.modulePullbackComplex.{z}).obj K).X n = f.modulePullback.{z}.obj (K.X n) := sorry

end modulePullbackComplex

namespace modulePullbackHomotopy

/-- The representative complex of homotopy-category pullback is degreewise module pullback of
the representative complex. -/
@[stacks 0G7E "homotopy representative", simp]
theorem obj_as.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (K : HomotopyCategory (ModuleCat.{z} Y) (up ℤ)) :
    ((f.modulePullbackHomotopy.{z}).obj K).as =
      (f.modulePullbackComplex.{z}).obj K.as := sorry

end modulePullbackHomotopy
end RingedSite.Hom
