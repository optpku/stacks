/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Comparing flatness of the structure module and morphism flatness
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The structure module is flat over the target at a point exactly when the
scheme morphism is flat at that point. -/
theorem structureSheaf_flatOverAt_iff_flatAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    flatOverAt (SheafOfModules.unit X.ringCatSheaf : X.Modules) f x ↔
      Scheme.Hom.flatAt f x := sorry

end AlgebraicGeometry.Scheme.Modules
