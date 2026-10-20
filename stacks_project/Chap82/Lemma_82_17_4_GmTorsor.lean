/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap76.Lemma_76_32_2
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup
import stacks_project.Chap82.Lemma_82_10_4_Pullback
import stacks_project.Chap82.Lemma_82_17_3_Torsor

/-!
# Import-isolated G_m-torsor and cycle pullback

The G_m-torsor of Lemma 82.17.3 and `Hom.flatPullback` of Lemma 82.10.4 cannot
be co-imported with meromorphic-section files. This module exposes those
names as opaque public wrappers, without the conflicting étale sheaf-compose
and geometric-point declarations.
-/

public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The canonical `G_m`-torsor of an invertible `𝒪_X`-module. -/
noncomputable def gmTorsor (L : X.Modules) [isInvertibleObject L] : AlgebraicSpace S :=
  Modules.gmTorsor L

/-- The structure morphism `q : T ⟶ X` of the `G_m`-torsor of `L`. -/
noncomputable def gmTorsorπ (L : X.Modules) [isInvertibleObject L] : gmTorsor L ⟶ X :=
  Modules.gmTorsorπ L

/-- The tautological trivialization `α : q^* L ≅ 𝒪_T`. -/
noncomputable def gmTorsorTriv (L : X.Modules) [isInvertibleObject L] :
    (Modules.pullback (gmTorsorπ L)).obj L ≅ 𝟙_ (gmTorsor L).Modules :=
  Modules.gmTorsorTriv L

/-- The structure morphism of the `G_m`-torsor is flat. -/
instance instFlat_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Flat (gmTorsorπ L) :=
  Modules.instFlat_gmTorsorπ L

/-- The structure morphism of the `G_m`-torsor has relative dimension `1`. -/
instance instRelativeDimension_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    RelativeDimension (gmTorsorπ L) 1 :=
  Modules.instRelativeDimension_gmTorsorπ L

/-- The structure morphism of the `G_m`-torsor is quasi-separated. -/
instance instQuasiSeparated_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    QuasiSeparated (gmTorsorπ L) :=
  Modules.instQuasiSeparated_gmTorsorπ L

/-- The structure morphism of the `G_m`-torsor is locally of finite type. -/
instance instLocallyOfFiniteType_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] :
    LocallyOfFiniteType (gmTorsorπ L) :=
  Modules.instLocallyOfFiniteType_gmTorsorπ L

/-- Composition of the `G_m`-torsor projection with a quasi-separated morphism
remains quasi-separated. -/
instance instQuasiSeparated_gmTorsorπ_comp {B : AlgebraicSpace S}
    (f : X ⟶ B) (L : X.Modules) [isInvertibleObject L] [QuasiSeparated f] :
    QuasiSeparated (gmTorsorπ L ≫ f) :=
  Modules.instQuasiSeparated_gmTorsorπ_comp f L

/-- Composition of the `G_m`-torsor projection with a locally finite type
morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_gmTorsorπ_comp {B : AlgebraicSpace S}
    (f : X ⟶ B) (L : X.Modules) [isInvertibleObject L]
    [LocallyOfFiniteType f] :
    LocallyOfFiniteType (gmTorsorπ L ≫ f) :=
  Modules.instLocallyOfFiniteType_gmTorsorπ_comp f L

/-- Pullback of an invertible module along the `G_m`-torsor remains invertible. -/
instance instIsInvertibleObject_pullback_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] :
    isInvertibleObject ((Modules.pullback (gmTorsorπ L)).obj L) :=
  Modules.instIsInvertibleObject_pullback_gmTorsorπ L

/-- Flat pullback of a cycle along a morphism of relative dimension `r`. -/
noncomputable def flatPullback {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  Hom.flatPullback pY pX δ f r hf k α

/-- Flat pullback sends the zero cycle to zero. -/
theorem flatPullback_zero {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    flatPullback pY pX δ f r hf k 0 = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
