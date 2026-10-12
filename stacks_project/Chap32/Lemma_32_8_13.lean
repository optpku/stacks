/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Immersion
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

/- Lemma 32.8.13: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f0` is an immersion and `f0` is locally of finite type, then some stagewise base change is an
immersion at a stage `i ≥ i0`. -/
@[stacks 0GTB] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_isImmersion_stage_of_limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    IsImmersion (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) →
      LocallyOfFiniteType f0 →
        ∃ (i : I) (hi0i : i0 ≤ i),
          IsImmersion (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))))

end

end AlgebraicGeometry
