/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Isomorphism
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable [∀ j, IsQuasiCompact (D.obj j)] [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
variable {Y0 Z0 : AlgebraicSpace S}
variable [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
variable [IsQuasiCompact Z0] [IsAbsolutelyQuasiSeparated Z0]

/- Lemma 70.5.8: in the notation and assumptions of Situation 70.5.5, if
`f0 : Y0 ⟶ Z0` is a morphism of algebraic spaces over `X0 = D.obj i0` whose
structure maps `Y0 ⟶ X0` and `Z0 ⟶ X0` are representable, `Y0` and `Z0` are
quasi-compact and absolutely quasi-separated, `f0` is locally of finite
presentation, and the limit base change `Y0 ×_{X0} X ⟶ Z0 ×_{X0} X` is an
isomorphism, then some stagewise base change `Y0 ×_{X0} X_i ⟶ Z0 ×_{X0} X_i`
is an isomorphism for a stage `i ≥ i0`.

The source explicitly states that this lemma is superseded by the stronger
isomorphism-descent lemma. The canonical theorem checked below proves this
conclusion without the representability assumptions on the structure maps.

The setup `QcqsMorphismBaseChange.ofCone D i0 Y0 Z0 c hc y0 z0 f0 hf0`
retains the specified limiting cone and the equation `f0 ≫ z0 = y0`.
Its `stageHom i hi0i` and `limitHom` are the canonical iterated-pullback
second projections representing these base changes to `X_i` and `X`. -/
@[stacks 084S] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.exists_isIso_stage_of_limitHom :
    ∀ (s : AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 Y0 Z0),
      IsIso s.limitHom →
        AlgebraicSpace.LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i), IsIso (s.stageHom i hi0i))

end
