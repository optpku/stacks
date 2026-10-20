/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Blowup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.AmpleFamily

/-- Every quasi-compact, quasi-separated scheme admits a finite-presentation, proper,
completely decomposed morphism from a scheme carrying an ample family of invertible modules. -/
theorem exists_proper_completelyDecomposed
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : Scheme.Hom.FinitePresentation f)
      (_ : IsProper f) (_ : Scheme.Hom.CompletelyDecomposed f)
      (ι : Type u) (L : ι → Y.Modules), AmpleFamily L := sorry

end AlgebraicGeometry.Scheme.Modules.AmpleFamily
