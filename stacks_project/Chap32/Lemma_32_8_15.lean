/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Surjective
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
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]

/- Lemma 32.8.15: in the notation and assumptions of Situation 32.8.1, if the limit base
change `f` of `f₀` is surjective and `f₀` is locally of finite presentation, then there exists
a stage `i ≥ i0` such that the stagewise base change `fᵢ` is surjective. -/
@[stacks 07RR] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_surjective_stage_of_limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    Surjective (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) →
      LocallyOfFinitePresentation f0 →
        ∃ (i : I) (hi0i : i0 ≤ i),
          Surjective (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))))

end

end AlgebraicGeometry
