/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AlgebraicSpaceColimit
import StacksCheckRecall

/-!
# Lemma 87.13.1

A directed colimit of algebraic spaces along thickenings is a formal algebraic
space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

/- Lemma 87.13.1: Let `S` be a scheme. Suppose given a directed set `Λ` and a
system of algebraic spaces `(X_λ, f_λμ)` over `Λ` where each
`f_λμ : X_λ ⟶ X_μ` is a thickening. Then `X = colim_λ X_λ` is a formal
algebraic space over `S`. The colimit is taken in fppf sheaves on
`(Sch/S)_fppf`. Nonempty indexing follows the source's directed-set convention.
The hypothesis `h_size` records the fixed-site condition from the chapter's
definition of formal algebraic spaces and its set-theoretic remark. -/
@[stacks 0AIU] #check
  (AlgebraicGeometry.IsFormalAlgebraicSpace.of_directedAlgebraicSpaceColimit :
    ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_algebraicSpace : ∀ i, AlgebraicGeometry.ChosenBigFppfSite.IsAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j),
      AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isRelativeThickening (F.map f))
    (c : Cocone F) (hc : IsColimit c)
    (h_size : AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables c.pt),
    AlgebraicGeometry.IsFormalAlgebraicSpace c.pt)

/- A sheaf with a directed algebraic-space thickening colimit presentation
and the fixed-site size condition is a formal algebraic space. -/
#check (AlgebraicGeometry.IsFormalAlgebraicSpace.of_isDirectedAlgebraicSpaceThickeningColimit :
    ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : AlgebraicGeometry.IsDirectedAlgebraicSpaceThickeningColimit D X)
    (h_size : AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables X),
    AlgebraicGeometry.IsFormalAlgebraicSpace X)
