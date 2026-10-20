/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback and internal Hom on ringed sites

This file owns the canonical comparison from the pullback of an internal Hom to the internal Hom
of the pullbacks.  The construction only needs the lax monoidal structure on module pullback; its
isomorphism criterion additionally uses monoidality, finite presentation, and exactness.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Functor.LaxMonoidal

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

section ComparisonAPI

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : Hom X Y) [f.modulePushforward.{z}.IsRightAdjoint]
variable [MonoidalCategory (ModuleCat.{z} Y)] [MonoidalClosed (ModuleCat.{z} Y)]
variable [MonoidalCategory (ModuleCat.{z} X)] [MonoidalClosed (ModuleCat.{z} X)]

section Comparison

variable [f.modulePullback.{z}.LaxMonoidal]

namespace PullbackInternalHom

/-- The uncurried evaluation map underlying the pullback--internal-Hom comparison. -/
@[stacks 0GMX "uncurried evaluation"]
noncomputable abbrev evaluation (F G : ModuleCat.{z} Y) :
    f.modulePullback.{z}.obj F ⊗ f.modulePullback.{z}.obj ((ihom F).obj G) ⟶
      f.modulePullback.{z}.obj G :=
  Functor.LaxMonoidal.InternalHom.evaluation f.modulePullback.{z} F G

end PullbackInternalHom

/-- Remark 18.27.3 (0GMX): pullback of an internal Hom maps canonically to the internal Hom of
the pullbacks. -/
@[stacks 0GMX]
noncomputable abbrev pullbackInternalHomComparison (F G : ModuleCat.{z} Y) :
    f.modulePullback.{z}.obj ((ihom F).obj G) ⟶
      (ihom (f.modulePullback.{z}.obj F)).obj (f.modulePullback.{z}.obj G) :=
  Functor.LaxMonoidal.InternalHom.comparison f.modulePullback.{z} F G

/-- Uncurrying the pullback--internal-Hom comparison recovers its defining evaluation map. -/
@[simp]
theorem uncurry_pullbackInternalHomComparison (F G : ModuleCat.{z} Y) :
    MonoidalClosed.uncurry (pullbackInternalHomComparison f F G) =
      PullbackInternalHom.evaluation f F G := sorry

/-- Evaluation after the pullback--internal-Hom comparison is the defining uncurried map. -/
@[simp]
theorem pullbackInternalHomComparison_ev (F G : ModuleCat.{z} Y) :
    f.modulePullback.{z}.obj F ◁ pullbackInternalHomComparison f F G ≫
        (ihom.ev (f.modulePullback.{z}.obj F)).app (f.modulePullback.{z}.obj G) =
      PullbackInternalHom.evaluation f F G := sorry

namespace PullbackInternalHom

/-- The pullback--internal-Hom comparison has the expanded naturality equation in its target
module. -/
theorem naturality_map (F : ModuleCat.{z} Y) {G H : ModuleCat.{z} Y} (g : G ⟶ H) :
    f.modulePullback.{z}.map ((ihom F).map g) ≫
        pullbackInternalHomComparison f F H =
      pullbackInternalHomComparison f F G ≫
        (ihom (f.modulePullback.{z}.obj F)).map (f.modulePullback.{z}.map g) := sorry

/-- The pullback--internal-Hom comparison is natural in its target module. -/
theorem naturality (F : ModuleCat.{z} Y) {G H : ModuleCat.{z} Y} (g : G ⟶ H) :
    (ihom F ⋙ f.modulePullback.{z}).map g ≫
        pullbackInternalHomComparison f F H =
      pullbackInternalHomComparison f F G ≫
        (f.modulePullback.{z} ⋙ ihom (f.modulePullback.{z}.obj F)).map g := sorry

/-- The pullback--internal-Hom comparison is contravariantly natural in its source module. -/
theorem naturality_left {E F : ModuleCat.{z} Y} (g : E ⟶ F) (G : ModuleCat.{z} Y) :
    pullbackInternalHomComparison f F G ≫
        (MonoidalClosed.pre (f.modulePullback.{z}.map g)).app (f.modulePullback.{z}.obj G) =
      f.modulePullback.{z}.map ((MonoidalClosed.pre g).app G) ≫
        pullbackInternalHomComparison f E G := sorry

/-- For a fixed source module, pullback--internal-Hom comparison is a natural transformation. -/
@[stacks 0GMX "natural comparison"]
noncomputable abbrev natTrans (F : ModuleCat.{z} Y) :
    ihom F ⋙ f.modulePullback.{z} ⟶
      f.modulePullback.{z} ⋙ ihom (f.modulePullback.{z}.obj F) :=
  Functor.LaxMonoidal.InternalHom.natTrans f.modulePullback.{z} F

/-- The component of `PullbackInternalHom.natTrans` is the canonical comparison map. -/
@[simp]
theorem natTrans_app (F G : ModuleCat.{z} Y) :
    (natTrans f F).app G = pullbackInternalHomComparison f F G := sorry

end PullbackInternalHom

end Comparison

end ComparisonAPI

section IsIso

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [∀ U : Y, HasWeakSheafify (Y.siteTopology.over U) AddCommGrpCat.{w}]
variable [∀ U : Y, (Y.siteTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : Hom X Y) [f.modulePushforward.{w}.IsRightAdjoint]
variable [MonoidalCategory (ModuleCat.{w} Y)] [MonoidalClosed (ModuleCat.{w} Y)]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalClosed (ModuleCat.{w} X)]
variable [f.modulePullback.{w}.Monoidal]

/-- Lemma 18.31.4 (0GN2): for a finitely presented source, an exact module pullback preserves
internal Hom up to the canonical comparison isomorphism. -/
@[stacks 0GN2]
theorem isIso_pullbackInternalHomComparison (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation]
    (h_exact : exactFunctor (ModuleCat.{w} Y) (ModuleCat.{w} X) f.modulePullback.{w}) :
    IsIso (pullbackInternalHomComparison f F G) := sorry

namespace PullbackInternalHom

/-- Lemma 18.31.4 (0GN2): pullback along a flat morphism commutes with internal Hom from a
finitely presented module. -/
@[stacks 0GN2 "flat specialization"]
theorem isIso_of_isFlat (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    IsIso (pullbackInternalHomComparison f F G) := sorry

/-- Flatness and finite presentation provide the canonical invertibility instance for the
pullback--internal-Hom comparison. -/
@[stacks 0GN2 "flat comparison isomorphism instance", instance]
noncomputable instance comparison_isIso_of_isFlat (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    IsIso (pullbackInternalHomComparison f F G) := sorry

/-- The named inverse of the flat pullback--internal-Hom comparison. -/
@[stacks 0GN2 "flat comparison inverse"]
noncomputable abbrev comparisonInv (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (ihom (f.modulePullback.{w}.obj F)).obj (f.modulePullback.{w}.obj G) ⟶
      f.modulePullback.{w}.obj ((ihom F).obj G) :=
  Functor.LaxMonoidal.InternalHom.comparisonInv f.modulePullback.{w} F G

/-- The flat pullback--internal-Hom comparison followed by its named inverse is the identity. -/
@[simp, stacks 0GN2 "flat comparison forward-inverse law"]
theorem comparison_comp_comparisonInv (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    pullbackInternalHomComparison f F G ≫ comparisonInv f F G = 𝟙 _ := sorry

/-- The named inverse followed by the flat pullback--internal-Hom comparison is the identity. -/
@[simp, stacks 0GN2 "flat comparison inverse-forward law"]
theorem comparisonInv_comp_comparison (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    comparisonInv f F G ≫ pullbackInternalHomComparison f F G = 𝟙 _ := sorry

/-- The pullback--internal-Hom comparison as an explicit isomorphism under flatness and finite
presentation. -/
@[stacks 0GN2 "flat comparison isomorphism"]
noncomputable def comparisonIso (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    f.modulePullback.{w}.obj ((ihom F).obj G) ≅
      (ihom (f.modulePullback.{w}.obj F)).obj (f.modulePullback.{w}.obj G) :=
  Functor.LaxMonoidal.InternalHom.comparisonIso f.modulePullback.{w} F G

/-- The forward map of the flat pullback--internal-Hom comparison isomorphism. -/
@[simp]
theorem comparisonIso_hom (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonIso f F G).hom = pullbackInternalHomComparison f F G := sorry

/-- The inverse map of the flat pullback--internal-Hom comparison isomorphism is the named
inverse comparison. -/
@[simp, stacks 0GN2 "flat comparison isomorphism inverse"]
theorem comparisonIso_inv (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonIso f F G).inv = comparisonInv f F G := sorry

/-- The named inverse comparison is natural in the target module. -/
@[stacks 0GN2 "flat inverse comparison naturality"]
theorem comparisonInv_naturality (F : ModuleCat.{w} Y)
    {G H : ModuleCat.{w} Y} (g : G ⟶ H)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (f.modulePullback.{w} ⋙ ihom (f.modulePullback.{w}.obj F)).map g ≫
        comparisonInv f F H =
      comparisonInv f F G ≫ (ihom F ⋙ f.modulePullback.{w}).map g := sorry

/-- For a finitely presented source, the named inverse comparisons form a natural
transformation in the target module. -/
@[stacks 0GN2 "flat inverse natural comparison"]
noncomputable def natTransInv (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    f.modulePullback.{w} ⋙ ihom (f.modulePullback.{w}.obj F) ⟶
      ihom F ⋙ f.modulePullback.{w} where
  app G := comparisonInv f F G
  naturality _ _ g := comparisonInv_naturality f F g

/-- A component of the inverse natural comparison is the named inverse comparison. -/
@[simp, stacks 0GN2 "flat inverse natural comparison component"]
theorem natTransInv_app (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (natTransInv f F).app G = comparisonInv f F G := sorry

/-- The forward and inverse comparison natural transformations compose to the identity. -/
@[simp, stacks 0GN2 "flat natural comparison forward-inverse law"]
theorem natTrans_comp_natTransInv (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    natTrans f F ≫ natTransInv f F = 𝟙 _ := sorry

/-- The inverse and forward comparison natural transformations compose to the identity. -/
@[simp, stacks 0GN2 "flat natural comparison inverse-forward law"]
theorem natTransInv_comp_natTrans (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    natTransInv f F ≫ natTrans f F = 𝟙 _ := sorry

/-- The forward and inverse comparison components compose to the identity. -/
@[simp, stacks 0GN2 "flat natural comparison component forward-inverse law"]
theorem natTrans_app_comp_natTransInv_app (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (natTrans f F).app G ≫ (natTransInv f F).app G = 𝟙 _ := sorry

/-- The inverse and forward comparison components compose to the identity. -/
@[simp, stacks 0GN2 "flat natural comparison component inverse-forward law"]
theorem natTransInv_app_comp_natTrans_app (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (natTransInv f F).app G ≫ (natTrans f F).app G = 𝟙 _ := sorry

/-- For a finitely presented source, the flat pullback--internal-Hom comparisons form a natural
isomorphism in the target module. -/
@[stacks 0GN2 "flat comparison natural isomorphism"]
noncomputable def comparisonNatIso (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    ihom F ⋙ f.modulePullback.{w} ≅
      f.modulePullback.{w} ⋙ ihom (f.modulePullback.{w}.obj F) where
  hom := natTrans f F
  inv := natTransInv f F
  hom_inv_id := natTrans_comp_natTransInv f F
  inv_hom_id := natTransInv_comp_natTrans f F

/-- Flatness and finite presentation make the whole target-variable comparison invertible. -/
@[stacks 0GN2 "flat comparison natural transformation isomorphism", instance]
noncomputable instance natTrans_isIso (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    IsIso (natTrans f F) := sorry

/-- The forward natural transformation of `comparisonNatIso` is the canonical comparison family. -/
@[stacks 0GN2 "flat comparison natural isomorphism hom", simp]
theorem comparisonNatIso_hom (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonNatIso f F).hom = natTrans f F := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the named inverse family. -/
@[stacks 0GN2 "flat comparison natural isomorphism inverse", simp]
theorem comparisonNatIso_inv (F : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonNatIso f F).inv = natTransInv f F := sorry

/-- A component of `comparisonNatIso` is the pointwise flat comparison isomorphism. -/
@[simp]
theorem comparisonNatIso_app (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonNatIso f F).app G = comparisonIso f F G := sorry

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp]
theorem comparisonNatIso_hom_app (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonNatIso f F).hom.app G = pullbackInternalHomComparison f F G := sorry

/-- The inverse component of `comparisonNatIso` is the named inverse comparison. -/
@[simp, stacks 0GN2 "flat comparison natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (F G : ModuleCat.{w} Y)
    [F.IsFinitePresentation] [IsFlat.{w} f] :
    (comparisonNatIso f F).inv.app G = comparisonInv f F G := sorry

end PullbackInternalHom

end IsIso

end RingedSite.Hom
