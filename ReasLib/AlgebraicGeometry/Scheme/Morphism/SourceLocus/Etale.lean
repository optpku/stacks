/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace CategoryTheory.MorphismProperty

/-- In a commutative square of schemes, source-locus membership is preserved and
reflected when both vertical morphisms are étale at the corresponding points. -/
theorem mem_sourceLocus_iff_of_etaleAt_commSq
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    {X' X Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (g : Y' ⟶ Y) (f : X ⟶ Y) (sq : CommSq f' g' g f) (x' : X')
    (hg' : g'.EtaleAt x') (hg : g.EtaleAt (f' x')) :
    g' x' ∈ P.sourceLocus f ↔ x' ∈ P.sourceLocus f' := sorry

end CategoryTheory.MorphismProperty
