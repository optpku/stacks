/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalGlueing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

universe u

/- 81.10.6.2: In Situation 81.10.6, to a triple (H, G, φ) one assigns the
𝒪_X-module Ker(j_* H ⊕ f_* G ⟶ (f ∘ j')_* (G|_V)), where j : U = X \ Z ⟶ X,
j' : V = Y \ f⁻¹(Z) ⟶ Y, and φ : (f|_V)^* H ⟶ G|_V.
The source triples have quasi-coherent components and invertible φ; the kernel
construction itself applies to arbitrary modules and overlap morphisms. -/
@[stacks 0AEX] #check (AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.reverse :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)), X.Modules)

/- Quasi-coherence of the reverse module under the qcqs and finite-presentation conditions. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.reverse.instIsQuasicoherent :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f] [FinitePresentation i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
    [H.IsQuasicoherent] [G.IsQuasicoherent], (reverse f i H G φ).IsQuasicoherent)
