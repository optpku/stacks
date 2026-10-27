/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedPushforwardComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section

universe u z

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] [UnivLE.{u + 1, z}]

/- Lemma 104.3.2 (1): the canonical lisse-étale module
pushforward restriction comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleDerivedPushforwardRestrictionComparison.instIsIso :
    ∀ (φ : X ⟶ Y) [Smooth φ], IsIso (lisseEtaleDerivedPushforwardRestrictionComparison.{u, z} φ))

/- Lemma 104.3.2 (2): the canonical lisse-étale abelian-sheaf
pushforward restriction comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedPushforwardRestrictionComparison.instIsIso :
    ∀ (φ : X ⟶ Y) [Smooth φ], IsIso (lisseEtaleAbelianDerivedPushforwardRestrictionComparison.{u, z} φ))

/- Lemma 104.3.2 (3): the canonical flat-fppf module
pushforward restriction comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.flatFppfDerivedPushforwardRestrictionComparison.instIsIso :
    ∀ (φ : X ⟶ Y) [Flat φ], IsIso (flatFppfDerivedPushforwardRestrictionComparison.{u, z} φ))

/- Lemma 104.3.2 (4): the canonical flat-fppf abelian-sheaf
pushforward restriction comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedPushforwardRestrictionComparison.instIsIso :
    ∀ (φ : X ⟶ Y) [Flat φ], IsIso (flatFppfAbelianDerivedPushforwardRestrictionComparison.{u, z} φ))

/- Lemma 104.3.2 (5): the canonical lisse-étale module
lower-shriek inverse-image comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleDerivedLowerShriekComparison.isIso :
    ∀ (φ : X ⟶ Y) [Smooth φ],
      ∀ (G : DerivedCategory (SheafOfModules.{z} (lisseEtaleInverseImageRingSheaf Y))),
      IsIso (lisseEtaleDerivedLowerShriekComparison φ G))

/- Lemma 104.3.2 (6): the canonical lisse-étale abelian-sheaf
lower-shriek inverse-image comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedLowerShriekComparison.isIso :
    ∀ (φ : X ⟶ Y) [Smooth φ],
      ∀ (G : DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z})),
      IsIso (lisseEtaleAbelianDerivedLowerShriekComparison φ G))

/- Lemma 104.3.2 (7): the canonical flat-fppf module
lower-shriek inverse-image comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.flatFppfDerivedLowerShriekComparison.isIso :
    ∀ (φ : X ⟶ Y) [Flat φ],
      ∀ (G : DerivedCategory (SheafOfModules.{z} (flatFppfInverseImageRingSheaf Y))),
      IsIso (flatFppfDerivedLowerShriekComparison φ G))

/- Lemma 104.3.2 (8): the canonical flat-fppf abelian-sheaf
lower-shriek inverse-image comparison is invertible on unbounded derived categories. -/
@[stacks 07AV] #check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedLowerShriekComparison.isIso :
    ∀ (φ : X ⟶ Y) [Flat φ],
      ∀ (G : DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z})),
      IsIso (flatFppfAbelianDerivedLowerShriekComparison φ G))

