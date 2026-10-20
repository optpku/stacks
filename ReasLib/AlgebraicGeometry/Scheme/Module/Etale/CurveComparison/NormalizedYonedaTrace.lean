/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NormalizedKummerTrace

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.AssociatedModule
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.NormalizedCurveTrace
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
variable {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Scheme.etaleRestriction j).op.HasLeftKanExtension F]
variable (n : ℕ) (h_pos : 0 < n) (h_n : IsUnit (n : k))

/-- The intrinsic compact roots coefficient used by the normalized trace. -/
abbrev intrinsicCompactRootsSheaf :=
  (Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
    (Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n)

/-- The actual Yoneda-product/trace map on compactly supported classes.
The second argument is an Ext class, not an assumed identification with
cohomology of a dual coefficient sheaf. -/
def yonedaCompactTrace
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a b : ℕ) (hab : a + b = 2)
    (x : ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F).H a)
    (e : Ext ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F)
      (intrinsicCompactRootsSheaf C j n) b) : ZMod n :=
  intrinsicCompactKummerTrace C j n h_pos h_n (x.comp e hab)

/-- Additivity in the compactly supported class follows from Yoneda composition. -/
theorem yonedaCompactTrace_add_left
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a b : ℕ) (hab : a + b = 2)
    (x y : ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F).H a)
    (e : Ext ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F)
      (intrinsicCompactRootsSheaf C j n) b) :
    yonedaCompactTrace C j n h_pos h_n F a b hab (x + y) e =
      yonedaCompactTrace C j n h_pos h_n F a b hab x e +
      yonedaCompactTrace C j n h_pos h_n F a b hab y e := by
  simp only [yonedaCompactTrace, Ext.add_comp, map_add]

/-- Additivity in the Ext class also uses the specified Yoneda product. -/
theorem yonedaCompactTrace_add_right
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a b : ℕ) (hab : a + b = 2)
    (x : ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F).H a)
    (e f : Ext ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F)
      (intrinsicCompactRootsSheaf C j n) b) :
    yonedaCompactTrace C j n h_pos h_n F a b hab x (e + f) =
      yonedaCompactTrace C j n h_pos h_n F a b hab x e +
      yonedaCompactTrace C j n h_pos h_n F a b hab x f := by
  simp only [yonedaCompactTrace, Ext.comp_add, map_add]

/-- A coefficient evaluation morphism supplies the degree-zero Ext class
by extension by zero and the actual degree-zero Yoneda embedding. -/
def coefficientEvaluationTrace
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : F ⟶ Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n)
    (x : ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F).H 2) : ZMod n :=
  yonedaCompactTrace C j n h_pos h_n F 2 0 (by decide) x
    (Ext.mk₀ ((Scheme.etaleExtensionByZero j AddCommGrpCat.{u + 1}).map e))

end AlgebraicGeometry.SchemeOverField.NormalizedCurveTrace
