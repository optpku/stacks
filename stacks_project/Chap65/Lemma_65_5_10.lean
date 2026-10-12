/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf.RelativelyRepresentable
public import ReasLib.CategoryTheory.Limits.Over.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type u)

/- Lemma 65.5.10: for a scheme `S` contained in `Sch_fppf` and a presheaf of sets
`F` on `(Sch/S)_fppf`, the following are equivalent: the diagonal `F ⟶ F ⨯ F` is
representable, every Yoneda section `yoneda.obj U ⟶ F` is representable, and every
pairwise fibre product `pullback ξ ξ'` of such sections is a representable
presheaf. -/
@[stacks 025W]
#check (Functor.relativelyRepresentable.diag_tfae F :
  [yoneda.relativelyRepresentable (diag F),
    ∀ (U : Over S) (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ,
    ∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      (pullback ξ ξ').IsRepresentable].TFAE)
