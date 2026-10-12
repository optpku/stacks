/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Canonical

import Mathlib.Tactic.CrossRefAttribute

/-!
# Family pullback and indexed-functor transport

This leaf compares transport of descent data through an identity-base indexed functor with
pullback along a map of indexing families.  It includes the resulting coherent square with
canonical descent data.
-/

@[expose] public section

universe t t' uC vC uF vF uG vG

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

variable {ι' : Type t'} {S' : C} {X' : ι' → C}
variable (f' : ∀ j, X' j ⟶ S')
variable {α : ι' → ι} {p : S' ⟶ S}
variable {p' : ∀ j, X' j ⟶ X (α j)}
variable (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

namespace PullFunctor.Comparison

/-- Naturality components of an indexed functor respect the overlap morphisms after pulling a
descent datum to another indexing family. -/
@[stacks 02ZD "indexed-functor pullback comparison compatibility"]
theorem app_comm
    (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄
    (g₁ : Y ⟶ X' j₁) (g₂ : Y ⟶ X' j₂)
    (hg₁ : g₁ ≫ f' j₁ = q) (hg₂ : g₂ ≫ f' j₂ = q) :
    (G.map g₁.op.toLoc).toFunctor.map
          ((H.naturality (p' j₁)).hom.app (D.obj (α j₁))) ≫
        ((H.mapDescentData f ⋙
          Pseudofunctor.DescentData.pullFunctor G w).obj D).hom
            q g₁ g₂ hg₁ hg₂ =
      ((Pseudofunctor.DescentData.pullFunctor F w ⋙
        H.mapDescentData f').obj D).hom
          q g₁ g₂ hg₁ hg₂ ≫
        (G.map g₂.op.toLoc).toFunctor.map
          ((H.naturality (p' j₂)).hom.app (D.obj (α j₂))) := sorry

/-- Pointwise comparison showing that transport of descent data commutes with pullback to
another indexing family. -/
@[stacks 02ZD "indexed-functor pullback comparison component"]
def app
    (D : F.DescentData f) :
    (Pseudofunctor.DescentData.pullFunctor F w ⋙
        H.mapDescentData f').obj D ≅
      (H.mapDescentData f ⋙
        Pseudofunctor.DescentData.pullFunctor G w).obj D :=
  Pseudofunctor.DescentData.isoMk
    (fun j ↦ (H.naturality (p' j)).app (D.obj (α j)))
    (app_comm H f f' w D)

/-- The pointwise comparison between descent-data transport and family pullback is natural in
the descent datum. -/
@[stacks 02ZD "indexed-functor pullback comparison naturality"]
theorem app_naturality
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) :
    (Pseudofunctor.DescentData.pullFunctor F w ⋙
        H.mapDescentData f').map φ ≫
        (app H f f' w D₂).hom =
      (app H f f' w D₁).hom ≫
        (H.mapDescentData f ⋙
          Pseudofunctor.DescentData.pullFunctor G w).map φ := sorry

/-- Transport through an identity-base indexed functor commutes, up to natural isomorphism,
with pullback of descent data to another indexing family. -/
@[stacks 02ZD "indexed-functor pullback comparison"]
def iso :
    Pseudofunctor.DescentData.pullFunctor F w ⋙
        H.mapDescentData f' ≅
      H.mapDescentData f ⋙
        Pseudofunctor.DescentData.pullFunctor G w :=
  NatIso.ofComponents
    (app H f f' w)
    (app_naturality H f f' w)

namespace Hom

/-- Forward components of the family-pullback comparison are the naturality components of the
indexed functor along the comparison arrows. -/
@[simp, stacks 02ZD "indexed-functor pullback comparison forward component"]
theorem app_hom
    (D : F.DescentData f) (j : ι') :
    ((iso H f f' w).hom.app D).hom j =
      (H.naturality (p' j)).hom.app (D.obj (α j)) := sorry

end Hom

namespace Inv

/-- Inverse components of the family-pullback comparison are inverse naturality components of
the indexed functor along the comparison arrows. -/
@[simp, stacks 02ZD "indexed-functor pullback comparison inverse component"]
theorem app_hom
    (D : F.DescentData f) (j : ι') :
    ((iso H f f' w).inv.app D).hom j =
      (H.naturality (p' j)).inv.app (D.obj (α j)) := sorry

end Inv

namespace Hom

/-- The family-pullback comparison is natural in modifications of identity-base indexed
functors. -/
@[stacks 02ZD "indexed-functor pullback comparison modification naturality"]
theorem modification_app
    {K : IndexedFunctor (𝟭 C) F G} (β : H ⟶ K)
    (D : F.DescentData f) :
    (iso H f f' w).hom.app D ≫
        (Pseudofunctor.DescentData.pullFunctor G w).map
          ((mapDescentData.natTrans f β).app D) =
      (mapDescentData.natTrans f' β).app
          ((Pseudofunctor.DescentData.pullFunctor F w).obj D) ≫
        (iso K f f' w).hom.app D := sorry

end Hom

namespace Inv

/-- Inverse form of naturality of the family-pullback comparison in an indexed-functor
modification. -/
@[stacks 02ZD "indexed-functor pullback comparison inverse modification naturality"]
theorem modification_app
    {K : IndexedFunctor (𝟭 C) F G} (β : H ⟶ K)
    (D : F.DescentData f) :
    (Pseudofunctor.DescentData.pullFunctor G w).map
          ((mapDescentData.natTrans f β).app D) ≫
        (iso K f f' w).inv.app D =
      (iso H f f' w).inv.app D ≫
        (mapDescentData.natTrans f' β).app
          ((Pseudofunctor.DescentData.pullFunctor F w).obj D) := sorry

end Inv

end PullFunctor.Comparison

namespace PullFunctor.Coherence.Hom

/-- The canonical-descent and family-pullback comparisons for an indexed functor form a
coherent square.  This component form follows the square from transported source descent data
to canonical target descent data and is the form used directly in applications. -/
@[stacks 02ZD "indexed-functor pullback coherent square"]
theorem app
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) :
    (PullFunctor.Comparison.iso H f f' w).hom.app
          ((F.toDescentData f).obj x) ≫
        (Pseudofunctor.DescentData.pullFunctor G w).map
          ((Canonical.Comparison.iso H f).hom.app x) ≫
        (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso G w).hom.app
          ((H.app S).obj x) =
      (H.mapDescentData f').map
          ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F w).hom.app x) ≫
        (Canonical.Comparison.iso H f').hom.app
          ((F.map p.op.toLoc).toFunctor.obj x) ≫
        (G.toDescentData f').map
          ((H.naturality p).hom.app x) := sorry

end PullFunctor.Coherence.Hom

namespace PullFunctor.Coherence.Inv

/-- Inverse component form of the coherent square relating canonical descent, family pullback,
and transport through an indexed functor. -/
@[stacks 02ZD "indexed-functor pullback coherent square inverse"]
theorem app
    (x : F.obj (LocallyDiscrete.mk (Opposite.op S))) :
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso G w).inv.app
          ((H.app S).obj x) ≫
        (Pseudofunctor.DescentData.pullFunctor G w).map
          ((Canonical.Comparison.iso H f).inv.app x) ≫
        (PullFunctor.Comparison.iso H f f' w).inv.app
          ((F.toDescentData f).obj x) =
      (G.toDescentData f').map
          ((H.naturality p).inv.app x) ≫
        (Canonical.Comparison.iso H f').inv.app
          ((F.map p.op.toLoc).toFunctor.obj x) ≫
        (H.mapDescentData f').map
          ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F w).inv.app x) := sorry

end PullFunctor.Coherence.Inv

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
