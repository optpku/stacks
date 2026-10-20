/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Graph
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Graph

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- The graph morphism compatibility surface. -/
#check (AlgebraicGeometry.SchemeOverField.graph :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.SchemeOverField k} (f : Y ⟶ X),
    Y.left ⟶ pullback X.hom Y.hom)

/- The first-projection computation for graph morphisms. -/
#check (AlgebraicGeometry.SchemeOverField.graph_fst :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.SchemeOverField k} (f : Y ⟶ X),
    AlgebraicGeometry.SchemeOverField.graph f ≫ pullback.fst X.hom Y.hom = f.left)

/- The second-projection computation for graph morphisms. -/
#check (AlgebraicGeometry.SchemeOverField.graph_snd :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.SchemeOverField k} (f : Y ⟶ X),
    AlgebraicGeometry.SchemeOverField.graph f ≫ pullback.snd X.hom Y.hom = 𝟙 Y.left)

/- The closed-immersion instance for graph morphisms. -/
#check (AlgebraicGeometry.SchemeOverField.graph_isClosedImmersion :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.SchemeOverField k} [AlgebraicGeometry.IsSeparated X.hom]
    (f : Y ⟶ X),
    AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.SchemeOverField.graph f))

/- The integral graph-cycle construction. -/
#check (AlgebraicGeometry.AlgebraicCycle.graph :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.SchemeOverField k}
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] [AlgebraicGeometry.IsSeparated X.hom]
    (f : Y ⟶ X),
    AlgebraicGeometry.AlgebraicCycle (pullback X.hom Y.hom) ℤ)

/- The pushforward formula for the integral graph cycle. -/
#check (AlgebraicGeometry.AlgebraicCycle.graph_def :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.SchemeOverField k}
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] [AlgebraicGeometry.IsSeparated X.hom]
    (f : Y ⟶ X),
    AlgebraicGeometry.AlgebraicCycle.graph f =
      AlgebraicGeometry.AlgebraicCycle.map
        (AlgebraicGeometry.SchemeOverField.graph f)
        (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ))
        (@AlgebraicGeometry.AlgebraicCycle.fundamental Y.left
          (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (fun _ ↦ (0 : ℤ)) 0))
