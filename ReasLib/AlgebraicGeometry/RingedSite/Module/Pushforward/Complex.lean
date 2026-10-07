module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward of complexes on ringed sites

Module pushforward acts degreewise on unbounded cochain complexes.  This is the direct-image
counterpart of `RingedSite.Hom.modulePullbackComplex`.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

namespace RingedSite.Hom

/-- Module pushforward applied degreewise to unbounded cochain complexes. -/
@[stacks 0FRE "complex pushforward"]
noncomputable abbrev modulePushforwardComplex.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) :
    CochainComplex (ModuleCat.{z} X) ℤ ⥤ CochainComplex (ModuleCat.{z} Y) ℤ :=
  f.modulePushforward.{z}.mapHomologicalComplex (up ℤ)

namespace modulePushforwardComplex

/-- In each degree, complex pushforward is the underlying module pushforward. -/
@[simp]
theorem obj_X.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) (K : CochainComplex (ModuleCat.{z} X) ℤ) (n : ℤ) :
    ((f.modulePushforwardComplex.{z}).obj K).X n =
      f.modulePushforward.{z}.obj (K.X n) := sorry

end modulePushforwardComplex

end RingedSite.Hom
