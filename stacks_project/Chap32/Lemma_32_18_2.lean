/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.18.2: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f₀` is quasi-finite and `f₀` is locally of finite type, then some stagewise base change is
quasi-finite at a stage `i ≥ i0`. -/
@[stacks 094M] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_quasiFinite_stage_of_limitHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}} {i0 : I}
      {X0 Y0 : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
      [CompactSpace X0] [QuasiSeparatedSpace X0]
      [CompactSpace Y0] [QuasiSeparatedSpace Y0]
      [∀ {i i' : I} (h : i ≤ i'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE h))]
      (s : AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange D i0 X0 Y0),
      AlgebraicGeometry.Scheme.Hom.QuasiFinite s.limitHom →
        AlgebraicGeometry.LocallyOfFiniteType s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i),
            AlgebraicGeometry.Scheme.Hom.QuasiFinite (s.stageHom i hi0i))
