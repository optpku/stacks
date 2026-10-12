/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_16_2_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.16.2: an integral morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, and a quasi-compact
open immersion `ι : V ⟶ Y` such that `f⁻¹V ⟶ V` is finite and of finite
presentation, realises `X` as a directed inverse limit of algebraic spaces
`Xᵢ` over `Y` whose structure maps `Xᵢ ⟶ Y` are finite and of finite
presentation and such that each comparison `f⁻¹V ⟶ Xᵢ⁻¹V` is an
isomorphism. -/
@[stacks 0GUM] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_integralFiniteApproximationOverOpen :
    ∀ {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.IsIntegralHom f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      (ι : V ⟶ Y)
      [AlgebraicSpace.IsOpenImmersion ι] [AlgebraicSpace.QuasiCompact ι]
      [AlgebraicSpace.IsFinite (openInverseImageTo f ι)]
      [AlgebraicSpace.FinitePresentation (openInverseImageTo f ι)],
      Nonempty (IntegralFiniteApproximationOverOpen f ι))
