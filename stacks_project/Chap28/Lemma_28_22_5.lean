/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.22.5 (1): a finite-type quasi-coherent module on a quasi-compact open subscheme
of a quasi-compact quasi-separated scheme extends to a finite-type quasi-coherent module on
the whole scheme. -/
@[stacks 0G41] #check
  (AlgebraicGeometry.Scheme.Modules.exists_finiteTypeQuasiCoherentExtension :
    ∀ {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (G : U.Modules) [G.IsQuasicoherent] [G.IsFiniteType],
      ∃ G' : X.Modules,
        G'.IsQuasicoherent ∧ G'.IsFiniteType ∧ Nonempty (G'.restrict j ≅ G))

/- Lemma 28.22.5 (2): a finitely presented module on a quasi-compact open subscheme of a
quasi-compact quasi-separated scheme extends to a finitely presented module on the whole
scheme. -/
@[stacks 0G41] #check
  (AlgebraicGeometry.Scheme.Modules.exists_finitePresentationExtension :
    ∀ {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (G : U.Modules) [G.IsFinitePresentation],
      ∃ G' : X.Modules, G'.IsFinitePresentation ∧ Nonempty (G'.restrict j ≅ G))
