/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap74.Definition_74_22_3_Pseudofunctor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.DescentData :
  (Xᵢ : I → AlgebraicSpace S) → (∀ i, Xᵢ i ⟶ X) → Type (max (u + 1) v))

variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.overlap Xᵢ f :
  (i j : I) → ChosenPullback (f i) (f j))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.tripleOverlap Xᵢ f :
  (i j k : I) → ChosenPullback₃ (DescentData.overlap Xᵢ f i j)
    (DescentData.overlap Xᵢ f j k) (DescentData.overlap Xᵢ f i k))

#check (CategoryTheory.Pseudofunctor.DescentData.hom_ext :
  ∀ {D E : DescentData Xᵢ f} {a b : D ⟶ E}, (∀ i, a.hom i = b.hom i) → a = b)
