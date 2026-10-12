/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Flat
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open MonoidalCategory MonObj

universe u

/- Lemma 39.6.2 (1): If `T` is flat over `S`, then multiplication after
`ψ ⊗ₘ 𝟙 G : T ⊗ G ⟶ G ⊗ G` is flat. -/
@[stacks 047H] #check
  (AlgebraicGeometry.GroupScheme.instFlatMulLeft :
    ∀ {S : Scheme.{u}} (G : Over S) [GrpObj G] (T : Over S)
      [AlgebraicGeometry.Flat T.hom] (ψ : T ⟶ G),
      AlgebraicGeometry.Flat (((ψ ⊗ₘ 𝟙 G) ≫ μ[G]).left))

/- Lemma 39.6.2 (2): If a group scheme is flat over `S`, then its multiplication
morphism is flat. -/
@[stacks 047H] #check
  (AlgebraicGeometry.GroupScheme.instFlatMul :
    ∀ {S : Scheme.{u}} (G : Over S) [GrpObj G] [AlgebraicGeometry.Flat G.hom],
      AlgebraicGeometry.Flat (μ[G].left))
