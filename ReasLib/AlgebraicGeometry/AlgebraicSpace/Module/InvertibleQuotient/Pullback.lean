/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.IsoClass

/-!
# Pullback of invertible quotients of algebraic-space modules

An epimorphism onto an invertible module pulls back to an epimorphism onto the
actual pulled-back module. These maps descend to compatible-isomorphism classes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

open CategoryTheory.InvertibleQuotient

/-- Pullback preserves epimorphic quotient maps of algebraic-space modules. -/
theorem pullbackMap_epi (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    Epi ((Modules.pullback f).map q.hom) := sorry

/-- Pull back the target and quotient morphism using the specified module functor. -/
def pullback (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback f).obj E) where
  object := (Modules.pullback f).obj q.object
  isInvertible := @Modules.isInvertibleObject_pullback S X Y f q.object q.isInvertible
  hom := (Modules.pullback f).map q.hom
  hom_epi := pullbackMap_epi f q

/-- The quotient target is the actual pullback of the original target. -/
@[simp]
theorem pullback_object (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    (pullback f q).object = (Modules.pullback f).obj q.object := rfl

/-- The quotient morphism is the image of the original quotient morphism. -/
@[simp]
theorem pullback_hom (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    (pullback f q).hom = (Modules.pullback f).map q.hom := rfl

/-- The target of the pulled-back quotient remains tensor-invertible. -/
instance instIsInvertible_pullback (f : X ⟶ Y)
    {E : Y.Modules} (q : CategoryTheory.InvertibleQuotient E) :
    isInvertibleObject ((Modules.pullback f).obj q.object) :=
  (pullback f q).isInvertible

/-- Pullback preserves compatible target isomorphisms between invertible quotients. -/
theorem pullback_rel (f : X ⟶ Y) {E : Y.Modules}
    {q q' : CategoryTheory.InvertibleQuotient E} (h : Rel q q') :
    Rel (pullback f q) (pullback f q') := sorry

/-- The actual quotient pullback descends to compatible-isomorphism classes. -/
def pullbackClass (f : X ⟶ Y) {E : Y.Modules} :
    IsoClass E → IsoClass ((Modules.pullback f).obj E) :=
  Quotient.map (pullback f) (fun _ _ ↦ pullback_rel f)

/-- The class of a representative pulls back to the class of its actual pullback. -/
@[simp]
theorem pullbackClass_mk (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    pullbackClass f (IsoClass.mk q) = IsoClass.mk (pullback f q) := rfl

end AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient
