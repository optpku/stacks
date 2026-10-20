module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Limit.ProperSupport
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry
open AlgebraicSpace

universe u

/- Lemma 70.12.3: in the notation and assumptions of Situation 70.6.1, let `F₀` be a
quasi-coherent finite-type module on `X₀`, write `F` and `Fᵢ` for its pullbacks to `X`
and `Xᵢ`, and assume `f₀` is locally of finite type. If the scheme-theoretic support of
`F` is proper over `Y`, then the scheme-theoretic support of `Fᵢ` is proper over `Yᵢ`
for some stage `i ≥ i₀`. -/
@[stacks 08K2] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_proper_schemeTheoreticSupport_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
      {X0 Y0 : AlgebraicSpace S}
      [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
      [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
      [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0)
      (F0 : X0.Modules) [F0.IsQuasicoherent] [F0.IsFiniteType],
      AlgebraicSpace.Proper
        ((AlgebraicSpace.Modules.schemeTheoreticSupport
          ((AlgebraicSpace.Modules.pullback s.limitSourceMap).obj F0)).ι ≫
          s.limitHom) →
        AlgebraicSpace.LocallyOfFiniteType s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Proper
            ((AlgebraicSpace.Modules.schemeTheoreticSupport
              ((AlgebraicSpace.Modules.pullback (s.stageSourceMap i hi0i)).obj F0)).ι ≫
              s.stageHom i hi0i))
