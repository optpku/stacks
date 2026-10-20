/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Kummer

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

namespace ActualEtaleRootsPullback

variable {X Y : Scheme.{u}}
variable (π : X ⟶ Y) (n : ℕ)
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : (Y.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Scheme.smallEtalePullback π).op.HasLeftKanExtension F]

/-- The additive sheaf `μₙ` on the small étale site of a curve. -/
noncomputable abbrev rootsOfUnityEtaleAddSheaf (Z : Scheme.{u}) (n : ℕ) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale Z) n

/-- Unfold `rootsOfUnityEtaleAddSheaf` as the Kummer kernel sheaf. -/
theorem rootsOfUnityEtaleAddSheaf_eq (Z : Scheme.{u}) (n : ℕ) :
    rootsOfUnityEtaleAddSheaf Z n =
      CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale Z) n := sorry

/-- Small étale sheaf pullback of additive sheaves is additive. -/
instance smallEtalePullback_sheafPullback_additive :
    ((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology).Additive := sorry

/-- Small étale sheaf pullback of additive sheaves preserves finite limits. -/
instance smallEtalePullback_sheafPullback_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits
      ((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology) := sorry

/-- Small étale sheaf pullback of additive sheaves preserves finite colimits. -/
instance smallEtalePullback_sheafPullback_preservesFiniteColimits_addCommGrp :
    PreservesFiniteColimits
      ((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology) := sorry

/-- Restriction of structure sheaves along `π`, as a map into the small étale
pushforward of `𝒪_X`. -/
noncomputable def smallEtaleStructureSheafPushforwardHom :
    smallCommStructureSheaf .etale Y ⟶
      ((Scheme.smallEtalePullback π).sheafPushforwardContinuous CommRingCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology).obj
        (smallCommStructureSheaf .etale X) :=
  ObjectProperty.homMk
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          (Scheme.Γ.map
            (Limits.pullback.fst (U.unop.hom) π).op)
      naturality := fun {_ _} _ ↦ sorry }

/-- Induced map on additive units sheaves on the small étale site of `Y`. -/
noncomputable def unitsAddSheafPushforwardHom :
    CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale Y) ⟶
      ((Scheme.smallEtalePullback π).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology).obj
        (CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale X)) :=
  CategoryTheory.Sheaf.unitsAddMap (smallEtaleStructureSheafPushforwardHom π) ≫
    ObjectProperty.homMk
      { app := fun U ↦
          AddCommGrpCat.ofHom
            { toFun := fun g ↦
                CategoryTheory.Sheaf.unitsAddSheafSection
                  (smallCommStructureSheaf .etale X)
                  (U := op ((Scheme.smallEtalePullback π).obj U.unop))
                  (CategoryTheory.Sheaf.unitsAddSheafUnit
                    (((Scheme.smallEtalePullback π).sheafPushforwardContinuous
                        CommRingCat.{u + 1}
                        Y.smallEtaleTopology X.smallEtaleTopology).obj
                      (smallCommStructureSheaf .etale X)) g)
              map_zero' := sorry
              map_add' := sorry }
        naturality := fun {_ _} _ ↦ sorry }

/-- Adjoint transpose of `unitsAddSheafPushforwardHom`, as pullback of units. -/
noncomputable def unitsAddSheafPullbackHom :
    ((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology).obj
      (CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale Y)) ⟶
    CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale X) :=
  ((Scheme.smallEtalePullback π).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology).homEquiv _ _ |>.symm
    (unitsAddSheafPushforwardHom π)

/-- Comparison of `μₙ` after small étale pullback, from the pulled-back Kummer kernel. -/
noncomputable def rootsOfUnityAddSheafPullbackHom :
    ((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology).obj
      (rootsOfUnityEtaleAddSheaf Y n) ⟶
    rootsOfUnityEtaleAddSheaf X n :=
  kernel.lift (CategoryTheory.Sheaf.unitsNsmul (smallCommStructureSheaf .etale X) n)
    (((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
          Y.smallEtaleTopology X.smallEtaleTopology).map
        (kernel.ι (CategoryTheory.Sheaf.unitsNsmul
          (smallCommStructureSheaf .etale Y) n)) ≫
      unitsAddSheafPullbackHom π)
    sorry

/-- The pullback of the terminal object of `Y.Etale` is isomorphic to the
terminal object of `X.Etale`. -/
instance smallEtalePullback_obj_terminal_isIso :
    IsIso (terminal.from ((Scheme.smallEtalePullback π).obj (⊤_ Y.Etale))) := sorry

/-- Canonical identification of the pulled-back constant sheaf of integers, as the
unit of small étale sheaf pullback against the constant sheaf adjunction. -/
noncomputable def constantAddSheafPullbackIso :
    ((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) ≅
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) :=
  ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        (terminalIsTerminal : IsTerminal (⊤_ Y.Etale))).comp
      ((Scheme.smallEtalePullback π).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology)).leftAdjointUniq
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (terminalIsTerminal.ofIso
        (asIso (terminal.from
          ((Scheme.smallEtalePullback π).obj (⊤_ Y.Etale)))).symm)) |>.app
    (AddCommGrpCat.of (ULift ℤ))

/-- Étale pullback `π*` on `H²(−, μₙ)`, as an additive map. -/
noncomputable def rootsOfUnityH2Pullback :
    CategoryTheory.Sheaf.H (rootsOfUnityEtaleAddSheaf Y n) 2 →+
      CategoryTheory.Sheaf.H (rootsOfUnityEtaleAddSheaf X n) 2 where
  toFun x :=
    CategoryTheory.Sheaf.H.map (rootsOfUnityAddSheafPullbackHom π n) 2
      ((Abelian.Ext.mk₀ (constantAddSheafPullbackIso π).inv).comp
        (((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
              Y.smallEtaleTopology X.smallEtaleTopology).mapExtAddHom
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift ℤ)))
          (rootsOfUnityEtaleAddSheaf Y n) 2 x)
        (zero_add (2 : ℕ)))
  map_zero' := sorry
  map_add' := sorry

/-- The component of `rootsOfUnityH2Pullback` after the constant-sheaf identification. -/
theorem rootsOfUnityH2Pullback_apply
    (x : CategoryTheory.Sheaf.H (rootsOfUnityEtaleAddSheaf Y n) 2) :
    rootsOfUnityH2Pullback π n x =
      CategoryTheory.Sheaf.H.map (rootsOfUnityAddSheafPullbackHom π n) 2
        ((Abelian.Ext.mk₀ (constantAddSheafPullbackIso π).inv).comp
          (((Scheme.smallEtalePullback π).sheafPullback AddCommGrpCat.{u + 1}
                Y.smallEtaleTopology X.smallEtaleTopology).mapExtAddHom
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift ℤ)))
            (rootsOfUnityEtaleAddSheaf Y n) 2 x)
          (zero_add (2 : ℕ))) := sorry

/-- `rootsOfUnityH2Pullback` preserves addition. -/
theorem rootsOfUnityH2Pullback_add
    (x y : CategoryTheory.Sheaf.H (rootsOfUnityEtaleAddSheaf Y n) 2) :
    rootsOfUnityH2Pullback π n (x + y) =
      rootsOfUnityH2Pullback π n x + rootsOfUnityH2Pullback π n y := sorry

end ActualEtaleRootsPullback
