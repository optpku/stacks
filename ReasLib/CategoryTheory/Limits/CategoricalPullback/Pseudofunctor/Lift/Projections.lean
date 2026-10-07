module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection Comparisons for Pointwise Categorical Pullback Lifts

This leaf identifies both indexed projections of a universal pointwise-pullback lift with its
input indexed functors. The cospan may lie over an arbitrary functor `u : C ⥤ D`, and the cone
may lie over an arbitrary functor `v : E ⥤ C`.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uE vE uF vF uG vG uH vH uK vK

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {u : C ⥤ D} {v : E ⥤ C}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}
variable {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}

namespace Pullback.Lift.Fst

/-- The objectwise comparison between the first projection of a pointwise-pullback lift and
the left input. The lift stores the left input object definitionally. -/
@[stacks 0040 "objectwise first projection of a pointwise categorical pseudo-pullback lift"]
noncomputable def isoObj
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((Pullback.Lift.ofCone L R A B e).comp
        (Pullback.Fst.indexedFunctor L R)).app U).obj x ≅
      (A.app U).obj x :=
  CategoryTheory.Iso.refl _

/-- The objectwise first-projection comparisons are natural in the source fiber. -/
theorem isoObj.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    {x y : K.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y) :
    (((Pullback.Lift.ofCone L R A B e).comp
          (Pullback.Fst.indexedFunctor L R)).app U).map φ ≫
        (isoObj L R A B e U y).hom =
      (isoObj L R A B e U x).hom ≫ (A.app U).map φ := sorry

/-- The component natural isomorphism identifying the first projection of a pointwise-pullback
lift with its left input. -/
@[stacks 0040 "fiberwise first projection of a pointwise categorical pseudo-pullback lift"]
noncomputable def isoApp
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    ((Pullback.Lift.ofCone L R A B e).comp
        (Pullback.Fst.indexedFunctor L R)).app U ≅ A.app U :=
  NatIso.ofComponents
    (isoObj L R A B e U)
    (fun φ ↦ isoObj.naturality L R A B e U φ)

/-- The forward arrow of the objectwise first-projection comparison is the identity. -/
@[simp]
theorem isoObj.hom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoObj L R A B e U x).hom = 𝟙 ((A.app U).obj x) := sorry

/-- The inverse arrow of the objectwise first-projection comparison is the identity. -/
@[simp]
theorem isoObj.inv
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoObj L R A B e U x).inv = 𝟙 ((A.app U).obj x) := sorry

/-- The forward component of the fiberwise first-projection comparison is its objectwise
identity comparison. -/
@[simp]
theorem isoApp.hom.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoApp L R A B e U).hom.app x =
      (isoObj L R A B e U x).hom := sorry

/-- The inverse component of the fiberwise first-projection comparison is its objectwise
identity comparison. -/
@[simp]
theorem isoApp.inv.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoApp L R A B e U).inv.app x =
      (isoObj L R A B e U x).inv := sorry

/-- Compatibility with reindexing of the first-projection comparison. -/
theorem iso.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((Pullback.Lift.ofCone L R A B e).comp
          (Pullback.Fst.indexedFunctor L R)).naturality f).hom.app x ≫
        (F.map ((𝟭 C).map (v.map f)).op.toLoc).toFunctor.map
          ((isoApp L R A B e U).hom.app x) =
      (isoApp L R A B e V).hom.app
          ((K.map f.op.toLoc).toFunctor.obj x) ≫
        (A.naturality f).hom.app x := sorry

/-- The first indexed projection of a pointwise-pullback lift is canonically isomorphic to its
left input indexed functor. -/
@[stacks 0040 "first indexed projection of a pointwise categorical pseudo-pullback lift"]
noncomputable def iso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) :
    (Pullback.Lift.ofCone L R A B e).comp
        (Pullback.Fst.indexedFunctor L R) ≅ A :=
  IndexedFunctor.mkIso
    (isoApp L R A B e)
    (fun f x ↦ iso.naturality L R A B e f x)

/-- Components of the first indexed projection comparison are its fiberwise comparison
isomorphisms. -/
@[simp]
theorem iso.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    IndexedFunctor.isoApp (iso L R A B e) U =
      isoApp L R A B e U := sorry

end Pullback.Lift.Fst

namespace Pullback.Lift.Snd

/-- The objectwise comparison between the second projection of a pointwise-pullback lift and
the right input. The lift stores the right input object definitionally. -/
@[stacks 0040 "objectwise second projection of a pointwise categorical pseudo-pullback lift"]
noncomputable def isoObj
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((Pullback.Lift.ofCone L R A B e).comp
        (Pullback.Snd.indexedFunctor L R)).app U).obj x ≅
      (B.app U).obj x :=
  CategoryTheory.Iso.refl _

/-- The objectwise second-projection comparisons are natural in the source fiber. -/
theorem isoObj.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    {x y : K.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y) :
    (((Pullback.Lift.ofCone L R A B e).comp
          (Pullback.Snd.indexedFunctor L R)).app U).map φ ≫
        (isoObj L R A B e U y).hom =
      (isoObj L R A B e U x).hom ≫ (B.app U).map φ := sorry

/-- The component natural isomorphism identifying the second projection of a
pointwise-pullback lift with its right input. -/
@[stacks 0040 "fiberwise second projection of a pointwise categorical pseudo-pullback lift"]
noncomputable def isoApp
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    ((Pullback.Lift.ofCone L R A B e).comp
        (Pullback.Snd.indexedFunctor L R)).app U ≅ B.app U :=
  NatIso.ofComponents
    (isoObj L R A B e U)
    (fun φ ↦ isoObj.naturality L R A B e U φ)

/-- The forward arrow of the objectwise second-projection comparison is the identity. -/
@[simp]
theorem isoObj.hom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoObj L R A B e U x).hom = 𝟙 ((B.app U).obj x) := sorry

/-- The inverse arrow of the objectwise second-projection comparison is the identity. -/
@[simp]
theorem isoObj.inv
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoObj L R A B e U x).inv = 𝟙 ((B.app U).obj x) := sorry

/-- The forward component of the fiberwise second-projection comparison is its objectwise
identity comparison. -/
@[simp]
theorem isoApp.hom.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoApp L R A B e U).hom.app x =
      (isoObj L R A B e U x).hom := sorry

/-- The inverse component of the fiberwise second-projection comparison is its objectwise
identity comparison. -/
@[simp]
theorem isoApp.inv.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (isoApp L R A B e U).inv.app x =
      (isoObj L R A B e U x).inv := sorry

/-- Compatibility with reindexing of the second-projection comparison. -/
theorem iso.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((Pullback.Lift.ofCone L R A B e).comp
          (Pullback.Snd.indexedFunctor L R)).naturality f).hom.app x ≫
        (G.map ((𝟭 C).map (v.map f)).op.toLoc).toFunctor.map
          ((isoApp L R A B e U).hom.app x) =
      (isoApp L R A B e V).hom.app
          ((K.map f.op.toLoc).toFunctor.obj x) ≫
        (B.naturality f).hom.app x := sorry

/-- The second indexed projection of a pointwise-pullback lift is canonically isomorphic to its
right input indexed functor. -/
@[stacks 0040 "second indexed projection of a pointwise categorical pseudo-pullback lift"]
noncomputable def iso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) :
    (Pullback.Lift.ofCone L R A B e).comp
        (Pullback.Snd.indexedFunctor L R) ≅ B :=
  IndexedFunctor.mkIso
    (isoApp L R A B e)
    (fun f x ↦ iso.naturality L R A B e f x)

/-- Components of the second indexed projection comparison are its fiberwise comparison
isomorphisms. -/
@[simp]
theorem iso.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    IndexedFunctor.isoApp (iso L R A B e) U =
      isoApp L R A B e U := sorry

end Pullback.Lift.Snd

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
