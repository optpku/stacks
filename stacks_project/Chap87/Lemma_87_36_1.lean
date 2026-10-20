/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Colimits
import StacksCheckRecall

/-!
# Lemma 87.36.1

A nonempty directed colimit of affine formal algebraic spaces along closed
immersions inducing isomorphisms on reductions is again an affine formal
algebraic space, subject to the fixed-site presentation condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

universe u v

/- Lemma 87.36.1: Let `S` be a scheme. Suppose given a directed set `Λ` and a
system of affine formal algebraic spaces `(X_λ, f_λμ)` over `Λ` where each
`f_λμ : X_λ ⟶ X_μ` is a closed immersion inducing an isomorphism
`X_λ,red ⟶ X_μ,red`. Then `X = colim_λ X_λ` is an affine formal algebraic
space over `S`. The transition hypothesis is the section's representable
thickening condition, and the colimit satisfies the fixed-site presentation
condition. -/
@[stacks 0GVM]
#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.of_directedColimit :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_affine : ∀ i, AlgebraicGeometry.IsAffineFormalAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j),
      AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isRelativeThickening (F.map f))
    (c : Cocone F) (hc : IsColimit c)
    (h_size : AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables c.pt),
    AlgebraicGeometry.IsAffineFormalAlgebraicSpace c.pt)
