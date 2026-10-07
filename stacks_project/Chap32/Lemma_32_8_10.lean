module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Etale
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/- Lemma 32.8.10: in the notation and assumptions of Situation 32.8.1, if the limit base
change of `f₀` is étale and `f₀` is locally of finite presentation, then some stagewise
base change `fᵢ` is étale for a stage `i ≥ i₀`. -/
@[stacks 07RP] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_etale_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
      [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
      [CompactSpace X0] [QuasiSeparatedSpace X0]
      [CompactSpace Y0] [QuasiSeparatedSpace Y0]
      [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
      (s : Scheme.Limit.QcqsMorphismBaseChange D i0 X0 Y0),
      Etale s.limitHom → LocallyOfFinitePresentation s.hom →
        ∃ (i : I) (hi0i : i0 ≤ i), Etale (s.stageHom i hi0i))
