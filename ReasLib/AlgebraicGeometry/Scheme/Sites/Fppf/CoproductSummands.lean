module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Coproduct

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- Every inclusion `F i ⟶ ∐ F` into an indexed coproduct of fppf sheaves is representable by
open and closed immersions (the indexed form of Stacks 0F15, as used in 02WP). -/
theorem sheafCoprodInj_isOpenAndClosedImmersion
    {S : Scheme.{u}} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (i : I) :
    (over ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf (c.inj i).hom := sorry

/-- An indexed coproduct inclusion of fppf sheaves identified with a scheme is
represented by an open and closed immersion. -/
theorem sheafCoprodι_isOpenAndClosedImmersion
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj) (i : I) :
    (over ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf
      ((c.inj i).hom ≫ e.inv) := sorry

/-- The open and closed summands of a represented indexed coproduct form a
coproduct in the slice over the base scheme. -/
theorem isColimit_sheafCoprod_summands
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj) :
    Nonempty (IsColimit (Cofan.mk U fun i ↦
      (sheafCoprodι_isOpenAndClosedImmersion hc e i).rep.snd
        (𝟙 (yoneda.obj U)))) := sorry

/-- Each indexed coproduct inclusion into a represented scheme is relatively
representable. -/
theorem sheafCoprodι_relativelyRepresentable
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj) (i : I) :
    yoneda.relativelyRepresentable ((c.inj i).hom ≫ e.inv) := sorry

/-- Every summand in an indexed coproduct represented by a scheme is
representable. -/
theorem sheafCoprod_summand_isRepresentable
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj) (i : I) :
    (F i).obj.IsRepresentable := sorry

/-- A represented pullback of an indexed coproduct inclusion is an open
immersion on schemes. -/
theorem isOpenImmersion_snd_of_isPullback_sheafCoprodι
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj)
    {V W : Over S} (i : I) (ξ : yoneda.obj V ⟶ yoneda.obj U)
    (fst : yoneda.obj W ⟶ (F i).obj) (snd : W ⟶ V)
    (h : IsPullback fst (yoneda.map snd) ((c.inj i).hom ≫ e.inv) ξ) :
    IsOpenImmersion snd.left := sorry

/-- A represented pullback of an indexed coproduct inclusion is a closed
immersion on schemes. -/
theorem isClosedImmersion_snd_of_isPullback_sheafCoprodι
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj)
    {V W : Over S} (i : I) (ξ : yoneda.obj V ⟶ yoneda.obj U)
    (fst : yoneda.obj W ⟶ (F i).obj) (snd : W ⟶ V)
    (h : IsPullback fst (yoneda.map snd) ((c.inj i).hom ≫ e.inv) ξ) :
    IsClosedImmersion snd.left := sorry

/-- After forgetting the slice over the base scheme, the underlying summands
form a coproduct of the underlying scheme of the represented object. -/
theorem isColimit_forget_sheafCoprod_summands
    {S : Scheme.{u}} {U : Over S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : yoneda.obj U ≅ c.pt.obj) :
    Nonempty (IsColimit (Cofan.mk U.left fun i ↦
      ((sheafCoprodι_isOpenAndClosedImmersion hc e i).rep.snd
        (𝟙 (yoneda.obj U))).left)) := sorry

end AlgebraicGeometry
