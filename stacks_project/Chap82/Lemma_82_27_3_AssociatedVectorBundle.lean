/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_4_8
public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_30_5_Flat
import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
import stacks_project.Chap76.Definition_76_6_5_Symmetric

/-!
# Associated vector bundle of a finite locally free module on an algebraic space

The total space of a finite locally free `𝒪_X`-module of rank `r` is the
relative spectrum of its symmetric algebra. Relative spectrum is imported
privately so this owner can be loaded beside Chow groups.
-/

public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A finite locally free module on an algebraic space is quasi-coherent. -/
instance instIsQuasicoherent_of_isFiniteLocallyFree (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] : E.IsQuasicoherent :=
  sorry

/-- The associated vector bundle of a finite locally free `𝒪_X`-module of
rank `r`. -/
noncomputable def associatedVectorBundleOfRank (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] : AlgebraicSpace S :=
  relativeSpec (SymmetricAlgebra.qcAlgebra E)

/-- The structure morphism of the associated vector bundle of a finite locally
free `𝒪_X`-module of rank `r`. -/
noncomputable def associatedVectorBundleOfRankπ (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    associatedVectorBundleOfRank E r ⟶ X :=
  relativeSpecπ (SymmetricAlgebra.qcAlgebra E)

/-- The structure morphism of the associated vector bundle is flat. -/
instance instFlat_associatedVectorBundleOfRankπ (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    Flat (associatedVectorBundleOfRankπ E r) :=
  sorry

/-- The structure morphism of the associated vector bundle has relative
dimension `r`. -/
instance instRelativeDimension_associatedVectorBundleOfRankπ (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    RelativeDimension (associatedVectorBundleOfRankπ E r) r :=
  sorry

/-- The structure morphism of the associated vector bundle is quasi-separated. -/
instance instQuasiSeparated_associatedVectorBundleOfRankπ (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    QuasiSeparated (associatedVectorBundleOfRankπ E r) :=
  sorry

/-- The structure morphism of the associated vector bundle is locally of finite
type. -/
instance instLocallyOfFiniteType_associatedVectorBundleOfRankπ (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    LocallyOfFiniteType (associatedVectorBundleOfRankπ E r) :=
  sorry

/-- Composition of the associated-vector-bundle projection with a quasi-separated
morphism remains quasi-separated. -/
instance instQuasiSeparated_associatedVectorBundleOfRankπ_comp {B : AlgebraicSpace S}
    (pX : X ⟶ B) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [QuasiSeparated pX] :
    QuasiSeparated (associatedVectorBundleOfRankπ E r ≫ pX) :=
  quasiSeparated_comp (associatedVectorBundleOfRankπ E r) pX

/-- Composition of the associated-vector-bundle projection with a locally finite
type morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_associatedVectorBundleOfRankπ_comp
    {B : AlgebraicSpace S} (pX : X ⟶ B) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [LocallyOfFiniteType pX] :
    LocallyOfFiniteType (associatedVectorBundleOfRankπ E r ≫ pX) :=
  locallyOfFiniteType_comp (associatedVectorBundleOfRankπ E r) pX

end AlgebraicGeometry.AlgebraicSpace
