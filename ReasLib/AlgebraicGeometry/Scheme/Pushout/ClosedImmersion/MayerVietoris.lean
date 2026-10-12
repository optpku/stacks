/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

noncomputable section

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion j]

/-- The restriction map from the first pushed-forward structure module to the
pushed-forward structure module along the common morphism. -/
def leftToCommon :
    (pushout.inl i j).pushforwardStructureModule ⟶ (common i j).pushforwardStructureModule :=
  (Scheme.Modules.pushforward (pushout.inl i j)).map
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp i (pushout.inl i j)).hom.app
      (SheafOfModules.unit Z.ringCatSheaf)

/-- The restriction map from the second pushed-forward structure module to the
pushed-forward structure module along the common morphism. -/
def rightToCommon :
    (pushout.inr i j).pushforwardStructureModule ⟶ (common i j).pushforwardStructureModule :=
  (Scheme.Modules.pushforward (pushout.inr i j)).map
      (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp j (pushout.inr i j)).hom.app
      (SheafOfModules.unit Z.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr (common_eq i j)).inv.app
      (SheafOfModules.unit Z.ringCatSheaf)

/-- The first map in the structure-sheaf Mayer–Vietoris sequence for a pushout of
closed immersions. -/
def toProduct :
    (SheafOfModules.unit (pushout i j).ringCatSheaf : (pushout i j).Modules) ⟶
      Limits.prod (pushout.inl i j).pushforwardStructureModule
        (pushout.inr i j).pushforwardStructureModule :=
  Limits.prod.lift
    (SheafOfModules.unitToPushforwardObjUnit (pushout.inl i j).toRingCatSheafHom)
    (SheafOfModules.unitToPushforwardObjUnit (pushout.inr i j).toRingCatSheafHom)

/-- The difference map in the structure-sheaf Mayer–Vietoris sequence for a pushout
of closed immersions. -/
def fromProduct :
    Limits.prod (pushout.inl i j).pushforwardStructureModule
        (pushout.inr i j).pushforwardStructureModule ⟶
      (common i j).pushforwardStructureModule :=
  Limits.prod.fst ≫ leftToCommon i j - Limits.prod.snd ≫ rightToCommon i j

/-- The first component of `toProduct` is the canonical map to the first pushed-forward
structure module. -/
theorem toProduct_fst :
    toProduct i j ≫ Limits.prod.fst =
      SheafOfModules.unitToPushforwardObjUnit (pushout.inl i j).toRingCatSheafHom := sorry

/-- The second component of `toProduct` is the canonical map to the second
pushed-forward structure module. -/
theorem toProduct_snd :
    toProduct i j ≫ Limits.prod.snd =
      SheafOfModules.unitToPushforwardObjUnit (pushout.inr i j).toRingCatSheafHom := sorry

/-- Restricting `fromProduct` to its first summand gives `leftToCommon`. -/
theorem inl_fromProduct :
    Limits.prod.lift (𝟙 _) 0 ≫ fromProduct i j = leftToCommon i j := sorry

/-- Restricting `fromProduct` to its second summand gives the negative of
`rightToCommon`. -/
theorem inr_fromProduct :
    Limits.prod.lift 0 (𝟙 _) ≫ fromProduct i j = -rightToCommon i j := sorry

/-- On sections, `leftToCommon` is the composite of pushforward of the structure map
with the canonical comparison for composition. -/
theorem leftToCommon_app (U : (pushout i j).Opens) :
    (leftToCommon i j).app U =
      ((Scheme.Modules.pushforward (pushout.inl i j)).map
          (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).app U ≫
        ((Scheme.Modules.pushforwardComp i (pushout.inl i j)).hom.app
          (SheafOfModules.unit Z.ringCatSheaf)).app U := sorry

/-- On sections, `rightToCommon` is the composite of pushforward of the structure map,
the comparison for composition, and transport along `common_eq`. -/
theorem rightToCommon_app (U : (pushout i j).Opens) :
    (rightToCommon i j).app U =
      ((Scheme.Modules.pushforward (pushout.inr i j)).map
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).app U ≫
        ((Scheme.Modules.pushforwardComp j (pushout.inr i j)).hom.app
          (SheafOfModules.unit Z.ringCatSheaf)).app U ≫
        ((Scheme.Modules.pushforwardCongr (common_eq i j)).inv.app
          (SheafOfModules.unit Z.ringCatSheaf)).app U := sorry

/-- The two maps in the structure-sheaf Mayer–Vietoris sequence compose to zero. -/
theorem toProduct_comp_fromProduct : toProduct i j ≫ fromProduct i j = 0 := sorry

/-- The structure-sheaf Mayer–Vietoris short complex of the pushout of two closed
immersions. -/
def structureSheafShortComplex : ShortComplex (pushout i j).Modules :=
  ShortComplex.mk (toProduct i j) (fromProduct i j) (toProduct_comp_fromProduct i j)

/-- The first map of `structureSheafShortComplex` is `toProduct`. -/
theorem structureSheafShortComplex_f :
    (structureSheafShortComplex i j).f = toProduct i j := sorry

/-- The second map of `structureSheafShortComplex` is `fromProduct`. -/
theorem structureSheafShortComplex_g :
    (structureSheafShortComplex i j).g = fromProduct i j := sorry

/-- The structure-sheaf Mayer–Vietoris complex of the pushout of two closed immersions
is short exact. -/
theorem structureSheafShortExact :
    (structureSheafShortComplex i j).ShortExact := sorry

end

end AlgebraicGeometry.Scheme.Pushout.ClosedImmersion
