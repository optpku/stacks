/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Power
public import ReasLib.CategoryTheory.Monoidal.Flat

/-!
# The ideal-tensor sequence of a closed immersion

For a closed immersion of schemes, this file gives the canonical sequence formed by tensoring
the kernel ideal with a module and mapping the module to the pushforward of its pullback. The
sequence is short exact when the module is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ClosedImmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- The map from the kernel ideal tensored with a module to the module, induced by the ideal's
inclusion into the structure sheaf and the left unitor. -/
noncomputable def idealTensorMap (F : X.Modules) :
    tensorObj (RingedSpace.Hom.idealSheaf i.toShHom) F ⟶ F :=
  tensorHom (RingedSpace.Hom.idealSheafι i.toShHom) (𝟙 F) ≫
    tensorHom (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom (𝟙 F) ≫
      (λ_ F).hom

/-- The unit map from a module to the pushforward of its pullback along a closed immersion. -/
noncomputable def restrictionMap (F : X.Modules) :
    F ⟶
      (SheafOfModules.pushforward (RingedSpace.Hom.toRingCatSheafHom i.toShHom)).obj
        ((SheafOfModules.pullback (RingedSpace.Hom.toRingCatSheafHom i.toShHom)).obj F) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.Hom.toRingCatSheafHom i.toShHom)).unit.app F

/-- The ideal-tensor map followed by restriction to the closed subscheme is zero. -/
theorem idealTensorMap_comp_restrictionMap (F : X.Modules) :
    idealTensorMap i F ≫ restrictionMap i F = 0 := sorry

/-- The canonical three-term complex associated to a closed immersion and a module. -/
noncomputable def sequence (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (idealTensorMap i F) (restrictionMap i F)
    (idealTensorMap_comp_restrictionMap i F)

/-- The ideal-tensor sequence of a flat module along a closed immersion is short exact. -/
theorem sequence_shortExact (F : X.Modules) [MonoidalCategory.IsFlat F] :
    (sequence i F).ShortExact := sorry

/-- The ideal-tensor sequence of every nonnegative tensor power of an invertible module along a
closed immersion is short exact. -/
theorem tensorPowerSequence_shortExact
    (L : X.Modules) [Invertible L] (n : ℕ) :
    (sequence i (RingedSpace.TensorPower.sheaf L n)).ShortExact := sorry

end AlgebraicGeometry.Scheme.Modules.ClosedImmersion
