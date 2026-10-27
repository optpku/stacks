/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Graph
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Over

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

open AlgebraicGeometry.ChowGroup

/- The graph Gysin action on total Chow homology. -/
#check (AlgebraicGeometry.ChowGroup.gysinMap :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r t : ℕ)
    [RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t],
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) X)
