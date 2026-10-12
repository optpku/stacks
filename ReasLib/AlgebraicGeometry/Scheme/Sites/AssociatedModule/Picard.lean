/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard

/-!
# Picard classes of associated modules on standard big scheme sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

variable (τ : StandardTopology) (X : Scheme.{u})

/-- The associated module of an invertible scheme module is tensor-invertible on a standard
big site. -/
instance bigCommIsInvertible (L : X.Modules) [isInvertibleObject L] :
    isInvertibleObject (bigComm τ X L) := sorry

/-- The Picard class of the associated module of the canonical representative of a scheme
Picard class. -/
noncomputable def picardMapFun (x : X.PicardGroup) :
    SheafOfModules.RingedSite.PicardGroup (τ.overTopology X) (bigCommStructureSheaf τ X) :=
  MonoidalCategory.PicardGroup.mk (bigComm τ X (Scheme.PicardGroup.repr x))

/-- Associated modules send the neutral scheme Picard class to the neutral big-site class. -/
theorem picardMapFun_zero : picardMapFun τ X 0 = 0 := sorry

/-- Associated modules carry addition of scheme Picard classes to addition of big-site classes. -/
theorem picardMapFun_add (x y : X.PicardGroup) :
    picardMapFun τ X (x + y) = picardMapFun τ X x + picardMapFun τ X y := sorry

/-- The additive homomorphism on Picard groups induced by associated modules. -/
noncomputable def picardMap :
    X.PicardGroup →+
      SheafOfModules.RingedSite.PicardGroup (τ.overTopology X) (bigCommStructureSheaf τ X) where
  toFun := picardMapFun τ X
  map_zero' := picardMapFun_zero τ X
  map_add' := picardMapFun_add τ X

/-- The associated-module Picard homomorphism sends the class of every invertible module to
the class of its associated module. -/
theorem picardMap_mk (L : X.Modules) [isInvertibleObject L] :
    picardMap τ X (Scheme.Modules.picardClass L) =
      MonoidalCategory.PicardGroup.mk (bigComm τ X L) := sorry

/-- Associated modules classify invertible modules on every standard big scheme site. -/
theorem picardMap_bijective : Function.Bijective (picardMap τ X) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
