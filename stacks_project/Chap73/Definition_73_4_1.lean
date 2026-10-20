/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap73.Definition_73_4_1_Precoverage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Definition 73.4.1 -/
@[stacks 041E] #check
  (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_etalePrecoverage_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X ↔
        (∀ i, Etale (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.etalePrecoverage :
  ∀ {S : Scheme.{u}}, Precoverage (AlgebraicSpace S))
