/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice

/-!
# Scheme-theoretic unions

The structure sheaves of two closed subschemes fit into a Mayer–Vietoris sequence for their
scheme-theoretic union and intersection, and the corresponding square of schemes is a pushout.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The structure sheaf of a closed subscheme of `S`, pushed forward to an `O_S`-module. -/
abbrev closedSubschemeStructureSheafOn (I : S.IdealSheafData) : S.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)

/-- The map of pushed-forward structure sheaves induced by an inclusion of closed
subschemes. -/
noncomputable def closedSubschemeStructureSheafMap {I J : S.IdealSheafData} (h : I ≤ J) :
    closedSubschemeStructureSheafOn I ⟶ closedSubschemeStructureSheafOn J :=
  (Scheme.Modules.pushforward I.subschemeι).map
      (SheafOfModules.unitToPushforwardObjUnit
        (Scheme.IdealSheafData.inclusion h).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (Scheme.IdealSheafData.inclusion h) I.subschemeι).hom.app
      (SheafOfModules.unit J.subscheme.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).hom.app
      (SheafOfModules.unit J.subscheme.ringCatSheaf)

/-- The first map in the structure-sheaf Mayer–Vietoris sequence for two closed
subschemes. -/
noncomputable abbrev schemeTheoreticUnionToProduct (I J : S.IdealSheafData) :
    closedSubschemeStructureSheafOn (I ⊓ J) ⟶
      Limits.prod (closedSubschemeStructureSheafOn I) (closedSubschemeStructureSheafOn J) :=
  Limits.prod.lift
    (closedSubschemeStructureSheafMap (inf_le_left : I ⊓ J ≤ I))
    (closedSubschemeStructureSheafMap (inf_le_right : I ⊓ J ≤ J))

/-- The second map in the structure-sheaf Mayer–Vietoris sequence for two closed
subschemes. -/
noncomputable abbrev schemeTheoreticProductToIntersection (I J : S.IdealSheafData) :
    Limits.prod (closedSubschemeStructureSheafOn I) (closedSubschemeStructureSheafOn J) ⟶
      closedSubschemeStructureSheafOn (I ⊔ J) :=
  Limits.prod.fst ≫ closedSubschemeStructureSheafMap (le_sup_left : I ≤ I ⊔ J) -
    Limits.prod.snd ≫ closedSubschemeStructureSheafMap (le_sup_right : J ≤ I ⊔ J)

/-- The two maps in the structure-sheaf Mayer–Vietoris sequence compose to zero. -/
theorem schemeTheoreticUnionToProduct_comp_schemeTheoreticProductToIntersection
    (I J : S.IdealSheafData) :
    schemeTheoreticUnionToProduct I J ≫ schemeTheoreticProductToIntersection I J = 0 := sorry

/-- The Mayer–Vietoris sequence of structure sheaves associated to two closed subschemes. -/
noncomputable def schemeTheoreticUnionShortComplex (I J : S.IdealSheafData) :
    ShortComplex S.Modules :=
  ShortComplex.mk (schemeTheoreticUnionToProduct I J)
    (schemeTheoreticProductToIntersection I J)
    (schemeTheoreticUnionToProduct_comp_schemeTheoreticProductToIntersection I J)

/-- The Mayer–Vietoris sequence of structure sheaves associated to two closed subschemes is
short exact. -/
theorem schemeTheoreticUnion_structureSheaf_shortExact (I J : S.IdealSheafData) :
    (schemeTheoreticUnionShortComplex I J).ShortExact := sorry

/-- The scheme-theoretic union of two closed subschemes is their pushout over their
scheme-theoretic intersection. -/
theorem schemeTheoreticUnion_isPushout (I J : S.IdealSheafData) :
    IsPushout
      (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) :
        Scheme.schemeTheoreticIntersection I J ⟶ I.subscheme)
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) :
        Scheme.schemeTheoreticIntersection I J ⟶ J.subscheme)
      (Scheme.IdealSheafData.inclusion (inf_le_left : I ⊓ J ≤ I) :
        I.subscheme ⟶ Scheme.schemeTheoreticUnion I J)
      (Scheme.IdealSheafData.inclusion (inf_le_right : I ⊓ J ≤ J) :
        J.subscheme ⟶ Scheme.schemeTheoreticUnion I J) := sorry

end AlgebraicGeometry
