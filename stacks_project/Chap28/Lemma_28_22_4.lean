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

/- Lemma 28.22.4: on a quasi-compact quasi-separated scheme, a morphism from a finitely
presented module on a quasi-compact open subscheme to the restriction of a quasi-coherent
module extends from a finitely presented module on the whole scheme. -/
@[stacks 01PI] #check
  (AlgebraicGeometry.Scheme.Modules.exists_finitePresentationMorphismExtension :
    ∀ {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (F : X.Modules) [F.IsQuasicoherent]
      (G : U.Modules) [G.IsFinitePresentation]
      (φ : G ⟶ F.restrict j),
      ∃ G' : X.Modules, G'.IsFinitePresentation ∧
        ∃ φ' : G' ⟶ F, ∃ e : G'.restrict j ≅ G,
          e.hom ≫ φ = (Scheme.Modules.restrictFunctor j).map φ')
