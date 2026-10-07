module

public import stacks_project.Chap70.Lemma_70_5_8_Isomorphism
public import stacks_project.Chap66.Definition_66_3_1_Separation
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry AlgebraicSpace
open Limit.QcqsMorphismBaseChange

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (c : Cone D) (hc : IsLimit c) (i0 : I)
variable [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
variable (Y0 Z0 : AlgebraicSpace S)
variable (y0 : Y0 ⟶ D.obj i0) (z0 : Z0 ⟶ D.obj i0) (f0 : Y0 ⟶ Z0)
variable (hf0 : f0 ≫ z0 = y0)
variable [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
variable [IsQuasiCompact Z0] [IsQuasiSeparated Z0]

/- Lemma 70.5.8: in the notation and assumptions of Situation 70.5.5, if
`f0 : Y0 ⟶ Z0` is a morphism of algebraic spaces over `X0 = D.obj i0` whose
structure maps `Y0 ⟶ X0` and `Z0 ⟶ X0` are representable, `Y0` and `Z0` are
quasi-compact and absolutely quasi-separated, `f0` is locally of finite
presentation, and the limit base change `Y0 ×_{X0} X ⟶ Z0 ×_{X0} X` is an
isomorphism, then some stagewise base change `Y0 ×_{X0} X_i ⟶ Z0 ×_{X0} X_i`
is an isomorphism for a stage `i ≥ i0`. -/
@[stacks 084S] #check
  (exists_isIso_stage_of_limitHom_of_relativelyRepresentable
    (ofCone D i0 Y0 Z0 c hc y0 z0 f0 hf0) :
    (∀ j, IsQuasiCompact (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated (D.obj j)) →
        IsAbsolutelyQuasiSeparated Y0 → IsAbsolutelyQuasiSeparated Z0 →
          yoneda.relativelyRepresentable y0 →
            yoneda.relativelyRepresentable z0 →
              IsIso (pullback.snd f0 (pullback.fst z0 (c.π.app i0))) →
                AlgebraicSpace.LocallyOfFinitePresentation f0 →
                  ∃ (i : I) (hi0i : i0 ≤ i),
                    IsIso (pullback.snd f0 (pullback.fst z0 (D.map (homOfLE hi0i)))))

end
