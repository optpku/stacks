/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Order.Directed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_11_1_Formal
public import stacks_project.Chap87.Lemma_87_18_1_Colimit

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

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

/-- Lemma 87.13.1: Let `S` be a scheme. Suppose given a directed set `Λ` and a
system of algebraic spaces `(X_λ, f_λμ)` over `Λ` where each
`f_λμ : X_λ ⟶ X_μ` is a thickening. Then `X = colim_λ X_λ` is a formal
algebraic space over `S`. The colimit is taken in fppf sheaves on
`(Sch/S)_fppf`. -/
@[stacks 0AIU]
theorem of_directedColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_algebraicSpace : ∀ i, ChosenBigFppfSite.IsAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j),
      (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (F.map f))
    (c : Cocone F) (hc : IsColimit c) :
    IsFormalAlgebraicSpace c.pt :=
  sorry

/-- A sheaf isomorphic to a directed colimit of algebraic spaces along
thickening transitions is a formal algebraic space. -/
theorem of_isDirectedAlgebraicSpaceThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAlgebraicSpaceThickeningColimit D X) :
    IsFormalAlgebraicSpace X :=
  sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
