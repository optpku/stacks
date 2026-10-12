/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Exactness.Composition.Naturality
public import ReasLib.CategoryTheory.Functor.Exactness.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence isomorphisms for exact-functor composition

The associator and unitors for ordinary functor composition lift canonically
to bundled exact functors.  Natural isomorphisms of exact functors also admit
horizontal composition in the bundled category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.ExactFunctor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

/-- Horizontal composition of isomorphisms of bundled exact functors. -/
@[stacks 015F "horizontal composition of exact-functor isomorphisms"]
noncomputable def hcompIso {F G : A ⥤ₑ B} (e : F ≅ G)
    {H I : B ⥤ₑ C} (f : H ≅ I) : F.comp H ≅ G.comp I :=
  ObjectProperty.isoMk (P := exactFunctor A C)
    (NatIso.hcomp ((ExactFunctor.forget A B).mapIso e)
      ((ExactFunctor.forget B C).mapIso f))

/-- The associator for composition of bundled exact functors. -/
@[stacks 015F "associator for exact-functor composition"]
noncomputable def associator (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (H : C ⥤ₑ D) : (F.comp G).comp H ≅ F.comp (G.comp H) :=
  ObjectProperty.isoMk (P := exactFunctor A D)
    (Functor.associator F.obj G.obj H.obj)

/-- The left unitor for composition of bundled exact functors. -/
@[stacks 015F "left unitor for exact-functor composition"]
noncomputable def leftUnitor (F : A ⥤ₑ B) :
    (ExactFunctor.id A).comp F ≅ F :=
  ObjectProperty.isoMk (P := exactFunctor A B) (Functor.leftUnitor F.obj)

/-- The right unitor for composition of bundled exact functors. -/
@[stacks 015F "right unitor for exact-functor composition"]
noncomputable def rightUnitor (F : A ⥤ₑ B) :
    F.comp (ExactFunctor.id B) ≅ F :=
  ObjectProperty.isoMk (P := exactFunctor A B) (Functor.rightUnitor F.obj)

namespace hcompIso

/-- The underlying forward transformation of exact-functor horizontal
composition is the ordinary horizontally composed transformation. -/
@[simp]
theorem hom_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    {H I : B ⥤ₑ C} (f : H ≅ I) :
    (hcompIso e f).hom.hom = NatTrans.hcomp e.hom.hom f.hom.hom := sorry

/-- The underlying inverse transformation of exact-functor horizontal
composition is the ordinary horizontally composed inverse. -/
@[simp]
theorem inv_hom {F G : A ⥤ₑ B} (e : F ≅ G)
    {H I : B ⥤ₑ C} (f : H ≅ I) :
    (hcompIso e f).inv.hom = NatTrans.hcomp e.inv.hom f.inv.hom := sorry

end hcompIso

namespace associator

/-- The underlying forward transformation of the exact associator is the
ordinary functor associator. -/
@[simp]
theorem hom_hom (F : A ⥤ₑ B) (G : B ⥤ₑ C) (H : C ⥤ₑ D) :
    (associator F G H).hom.hom =
      (Functor.associator F.obj G.obj H.obj).hom := sorry

/-- The underlying inverse transformation of the exact associator is the
ordinary inverse associator. -/
@[simp]
theorem inv_hom (F : A ⥤ₑ B) (G : B ⥤ₑ C) (H : C ⥤ₑ D) :
    (associator F G H).inv.hom =
      (Functor.associator F.obj G.obj H.obj).inv := sorry

end associator

namespace leftUnitor

/-- The underlying forward transformation of the exact left unitor is the
ordinary left unitor. -/
@[simp]
theorem hom_hom (F : A ⥤ₑ B) :
    (leftUnitor F).hom.hom = (Functor.leftUnitor F.obj).hom := sorry

/-- The underlying inverse transformation of the exact left unitor is the
ordinary inverse left unitor. -/
@[simp]
theorem inv_hom (F : A ⥤ₑ B) :
    (leftUnitor F).inv.hom = (Functor.leftUnitor F.obj).inv := sorry

end leftUnitor

namespace rightUnitor

/-- The underlying forward transformation of the exact right unitor is the
ordinary right unitor. -/
@[simp]
theorem hom_hom (F : A ⥤ₑ B) :
    (rightUnitor F).hom.hom = (Functor.rightUnitor F.obj).hom := sorry

/-- The underlying inverse transformation of the exact right unitor is the
ordinary inverse right unitor. -/
@[simp]
theorem inv_hom (F : A ⥤ₑ B) :
    (rightUnitor F).inv.hom = (Functor.rightUnitor F.obj).inv := sorry

end rightUnitor

end CategoryTheory.ExactFunctor
