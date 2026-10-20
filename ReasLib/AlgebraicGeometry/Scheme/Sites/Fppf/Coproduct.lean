/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry

/-- The inclusion of the first sheaf into a binary coproduct is representable by
open and closed immersions. -/
theorem sheafCoprodInl_isOpenAndClosedImmersion
    {S : Scheme.{u}} {F G : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : BinaryCofan F G} (hc : IsColimit c) :
    (over ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf c.inl.hom := sorry

/-- The inclusion of the second sheaf into a binary coproduct is representable by
open and closed immersions. -/
theorem sheafCoprodInr_isOpenAndClosedImmersion
    {S : Scheme.{u}} {F G : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : BinaryCofan F G} (hc : IsColimit c) :
    (over ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf c.inr.hom := sorry

/-- The inclusion of the first sheaf into a binary coproduct is relatively representable. -/
theorem sheafCoprodInl_relativelyRepresentable
    {S : Scheme.{u}} {F G : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : BinaryCofan F G} (hc : IsColimit c) :
    yoneda.relativelyRepresentable c.inl.hom := sorry

/-- A represented pullback of the first coproduct inclusion along a Yoneda section
is an open immersion. -/
theorem isOpenImmersion_snd_of_isPullback_sheafCoprodInl
    {S : Scheme.{u}} {F G : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : BinaryCofan F G} (hc : IsColimit c) {U V : Over S}
    (ξ : yoneda.obj U ⟶ c.pt.obj) (fst : yoneda.obj V ⟶ F.obj) (snd : V ⟶ U)
    (h : IsPullback fst (yoneda.map snd) c.inl.hom ξ) :
    IsOpenImmersion snd.left := sorry

/-- A represented pullback of the first coproduct inclusion along a Yoneda section
is a closed immersion. -/
theorem isClosedImmersion_snd_of_isPullback_sheafCoprodInl
    {S : Scheme.{u}} {F G : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : BinaryCofan F G} (hc : IsColimit c) {U V : Over S}
    (ξ : yoneda.obj U ⟶ c.pt.obj) (fst : yoneda.obj V ⟶ F.obj) (snd : V ⟶ U)
    (h : IsPullback fst (yoneda.map snd) c.inl.hom ξ) :
    IsClosedImmersion snd.left := sorry

end AlgebraicGeometry
