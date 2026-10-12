/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Functoriality

import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical descent and indexed-functor transport

This leaf gives the natural isomorphism comparing canonical descent data before and after
transport through an identity-base indexed functor, together with its component and modification
computation rules.
-/

@[expose] public section

universe t uC vC uF vF uG vG

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

namespace Canonical.Comparison

/-- The component naturality isomorphisms of an indexed functor respect the compatibility
morphisms in the canonical descent data of an object. -/
@[stacks 026D "canonical descent transport comparison compatibility"]
theorem app_comm
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S)))
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.map
          ((H.naturality (f i₁)).hom.app x) ≫
        ((H.app S ⋙ G.toDescentData f).obj x).hom
          q f₁ f₂ hf₁ hf₂ =
      ((F.toDescentData f ⋙ H.mapDescentData f).obj x).hom
          q f₁ f₂ hf₁ hf₂ ≫
        (G.map f₂.op.toLoc).toFunctor.map
          ((H.naturality (f i₂)).hom.app x) := sorry

/-- Pointwise comparison between first forming canonical descent data and then transporting it,
and first transporting the object and then forming canonical descent data. -/
@[stacks 026D "canonical descent transport comparison component"]
def app
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) :
    (F.toDescentData f ⋙ H.mapDescentData f).obj x ≅
      (H.app S ⋙ G.toDescentData f).obj x :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦ (H.naturality (f i)).app x)
    (app_comm H f x)

/-- The pointwise canonical-descent comparison is natural in the object over the base. -/
@[stacks 026D "canonical descent transport comparison naturality"]
theorem app_naturality
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op S))} (φ : x ⟶ y) :
    (F.toDescentData f ⋙ H.mapDescentData f).map φ ≫
        (app H f y).hom =
      (app H f x).hom ≫
        (H.app S ⋙ G.toDescentData f).map φ := sorry

/-- Canonical descent commutes, up to natural isomorphism, with an indexed functor over the
identity base functor. -/
@[stacks 026D "canonical descent transport comparison"]
def iso :
    F.toDescentData f ⋙ H.mapDescentData f ≅
      H.app S ⋙ G.toDescentData f :=
  NatIso.ofComponents
    (app H f)
    (app_naturality H f)

namespace Hom

/-- The forward component of the canonical-descent comparison is the naturality comparison of
the indexed functor. -/
@[simp, stacks 026D "canonical descent transport forward component"]
theorem app_hom
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) (i : ι) :
    ((iso H f).hom.app x).hom i =
      (H.naturality (f i)).hom.app x := sorry

end Hom

namespace Inv

/-- The inverse component of the canonical-descent comparison is the inverse naturality
comparison of the indexed functor. -/
@[simp, stacks 026D "canonical descent transport inverse component"]
theorem app_hom
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) (i : ι) :
    ((iso H f).inv.app x).hom i =
      (H.naturality (f i)).inv.app x := sorry

end Inv

namespace Hom

/-- The canonical-descent comparison is natural in modifications of identity-base indexed
functors. -/
@[stacks 026D "canonical descent transport modification naturality"]
theorem modification_app
    {K : IndexedFunctor (𝟭 C) F G} (α : H ⟶ K)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) :
    (iso H f).hom.app x ≫
        (G.toDescentData f).map ((α.app S).app x) =
      (mapDescentData.natTrans f α).app ((F.toDescentData f).obj x) ≫
        (iso K f).hom.app x := sorry

end Hom

namespace Inv

/-- Inverse form of naturality of the canonical-descent comparison in an indexed-functor
modification. -/
@[stacks 026D "canonical descent transport inverse modification naturality"]
theorem modification_app
    {K : IndexedFunctor (𝟭 C) F G} (α : H ⟶ K)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) :
    (G.toDescentData f).map ((α.app S).app x) ≫
        (iso K f).inv.app x =
      (iso H f).inv.app x ≫
        (mapDescentData.natTrans f α).app
          ((F.toDescentData f).obj x) := sorry

end Inv

end Canonical.Comparison

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
