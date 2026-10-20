/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.Connecting
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u

/- Definition 111.41.2: for a short exact sequence 0 → F₁ → F₂ → F₃ → 0 of abelian
sheaves on a topological space X, the boundary map δ : H⁰(X, F₃) → check H¹(X, F₁)
is `TopCat.Sheaf.Cohomology.Cech.delta`. On a global section τ, choose an open cover
with local F₂-lifts τ̃ᵢ; then δ(τ) is the global Čech class of the F₁-valued 1-cochain
(i₀, i₁) ↦ τ̃_{i₀}|U_{i₀i₁} − τ̃_{i₁}|U_{i₀i₁}. -/
@[stacks 02AP]
#check (@TopCat.Sheaf.Cohomology.Cech.delta :
  ∀ {X : TopCat.{u}} {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}, S.ShortExact →
    ((TopCat.Presheaf.Cech.Colimit.universeLift.{u}).obj (S.X₃.presheaf.obj (op ⊤)) ⟶
      TopCat.Sheaf.Cohomology.Cech.cohomology.{u, u, u} S.X₁ 1))

#check TopCat.Sheaf.Cohomology.Cech.delta_spec

#check TopCat.Sheaf.Cohomology.Cech.cochain_apply
