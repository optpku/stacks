/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
import StacksCheckRecall

/-!
# Limit-preserving 1-morphisms are limit preserving on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
limit preserving in the sense of Definition 102.3.1 is limit preserving on
objects in the sense of Section 97.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 102.3.2: Let `S` be a scheme. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf`. If `f` is limit
preserving (Definition 102.3.1), then `f` is limit preserving on objects
(Criteria for Representability, Section 97.5). -/
@[stacks 0CMS]
#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.toLimitPreservingOnObjects :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    (f : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.LimitPreserving f],
    AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects f)
