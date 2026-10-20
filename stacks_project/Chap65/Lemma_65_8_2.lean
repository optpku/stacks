/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.CoproductSummands
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

universe u v

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {U : Over S} {I : Type v}
variable {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
variable {c : Cofan F}
variable (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj) (i : I)
variable {V W : Over S} (ξ : yoneda.obj V ⟶ yoneda.obj U)
variable (fst : yoneda.obj W ⟶ (F i).obj) (snd : W ⟶ V)
variable (h : IsPullback fst (yoneda.map snd) ((c.inj i).hom ≫ e.inv) ξ)

/- Lemma 65.8.2: if a scheme `U` over `S` is isomorphic, as an fppf sheaf on
`Over S`, to a coproduct of sheaves `F i`, then every `F i` is represented by
an open and closed subscheme of `U`, and these subschemes form a coproduct. -/
@[stacks 02WO]
#check
  (AlgebraicGeometry.sheafCoprodι_isOpenAndClosedImmersion hc e i :
    (over ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf
      ((c.inj i).hom ≫ e.inv))

#check
  (AlgebraicGeometry.isColimit_sheafCoprod_summands hc e :
    Nonempty (IsColimit (Cofan.mk U fun i ↦
      (AlgebraicGeometry.sheafCoprodι_isOpenAndClosedImmersion hc e i).rep.snd
        (𝟙 (yoneda.obj U)))))

#check
  (AlgebraicGeometry.sheafCoprodι_relativelyRepresentable hc e i :
    yoneda.relativelyRepresentable ((c.inj i).hom ≫ e.inv))

#check
  (AlgebraicGeometry.sheafCoprod_summand_isRepresentable hc e i :
    (F i).obj.IsRepresentable)

#check
  (AlgebraicGeometry.isOpenImmersion_snd_of_isPullback_sheafCoprodι hc e i
      ξ fst snd h : IsOpenImmersion snd.left)

#check
  (AlgebraicGeometry.isClosedImmersion_snd_of_isPullback_sheafCoprodι hc e i
      ξ fst snd h : IsClosedImmersion snd.left)

#check
  (AlgebraicGeometry.isColimit_forget_sheafCoprod_summands hc e :
    Nonempty (IsColimit (Cofan.mk U.left fun i ↦
      ((AlgebraicGeometry.sheafCoprodι_isOpenAndClosedImmersion hc e i).rep.snd
        (𝟙 (yoneda.obj U))).left)))

end AlgebraicGeometry
