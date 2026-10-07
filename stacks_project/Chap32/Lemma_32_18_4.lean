module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeDimension.MorphismBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.18.4: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f₀` has relative dimension `d`, and `f₀` is locally of finite presentation, then some
stagewise base change has relative dimension `d`. -/
@[stacks 0EY2] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_relativeDimension_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}} {i0 : I}
      {X0 Y0 : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
      [CompactSpace X0] [QuasiSeparatedSpace X0]
      [CompactSpace Y0] [QuasiSeparatedSpace Y0]
      [∀ {i i' : I} (h : i ≤ i'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE h))]
      (s : AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange D i0 X0 Y0) (d : ℕ),
      AlgebraicGeometry.Scheme.Hom.RelativeDimension s.limitHom d →
        AlgebraicGeometry.LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i),
            AlgebraicGeometry.Scheme.Hom.RelativeDimension (s.stageHom i hi0i) d)
