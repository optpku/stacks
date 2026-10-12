/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Definition_87_23_2_AdicStar

/-!
# Lemma 87.10.1

For an affine formal algebraic space, a sequential system of affine thickenings
with sheaf colimit isomorphic to `X` is equivalent to a directed affine
thickening presentation whose index type is countable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- Lemma 87.10.1: Let `S` be a scheme. Let `X` be an affine formal algebraic
space over `S`. The following are equivalent: there exists a sequential system
of thickenings of affine schemes over `S` whose sheaf colimit is isomorphic to
`X`, and there exists a directed affine thickening colimit presentation of `X`
as in Definition 87.9.1 whose index type `Λ` is countable. -/
@[stacks 0AII]
theorem exists_natDirectedAffineThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (∃ D : ℕ ⥤ 𝒮.bigAffineSite S, IsNatDirectedAffineThickeningColimit D X) ↔
      (∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (_ : Countable Λ) (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X) := sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
