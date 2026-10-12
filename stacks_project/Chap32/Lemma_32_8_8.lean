/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteLocallyFree
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i0 : I)
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
variable (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
variable [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
variable [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]

/- Lemma 32.8.8 (1): in the notation and assumptions of Situation 32.8.1, if the limit base
change of `f_0` is finite locally free and `f_0` is locally of finite presentation, then some
stagewise base change `f_i` is finite locally free for a stage `i >= i0`. -/
@[stacks 06AC] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_isFiniteLocallyFree_stage_of_limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    IsFiniteLocallyFree (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) →
      LocallyOfFinitePresentation f0 →
        ∃ (i : I) (hi0i : i0 ≤ i),
          IsFiniteLocallyFree
            (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))))

/- Lemma 32.8.8 (2): in the notation and assumptions of Situation 32.8.1, if the limit base
change of `f_0` is finite locally free of degree `d` and `f_0` is locally of finite presentation,
then some stagewise base change `f_i` is finite locally free of degree `d` for a stage `i >= i0`.
-/
@[stacks 06AC] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_isFiniteLocallyFreeOfRank_stage_of_limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    ∀ d : ℕ,
      IsFiniteLocallyFreeOfRank (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) d →
        LocallyOfFinitePresentation f0 →
          ∃ (i : I) (hi0i : i0 ≤ i),
            IsFiniteLocallyFreeOfRank
              (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) d)

end

end AlgebraicGeometry
