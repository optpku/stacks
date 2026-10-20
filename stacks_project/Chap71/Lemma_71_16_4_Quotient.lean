/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.Conormal
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.IsoClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleQuotient.Pullback
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Pullback of invertible quotients of algebraic-space modules

Invertible quotients of modules on algebraic spaces, and their
compatible-isomorphism classes, pull back along morphisms of algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace InvertibleQuotient

variable {S : Scheme.{u}}

open CategoryTheory.InvertibleQuotient

/-- Compatible source and target isomorphisms induce an isomorphism of conormal objects of
invertible quotients of modules on the same algebraic space. -/
def conormalObjectIsoOf {X : AlgebraicSpace S} {E E' : X.Modules}
    (q : CategoryTheory.InvertibleQuotient E) (q' : CategoryTheory.InvertibleQuotient E')
    (sourceIso : E ≅ E') (targetIso : q.object ≅ q'.object)
    (comm : q.hom ≫ targetIso.hom = sourceIso.hom ≫ q'.hom) :
    conormalObject q ≅ conormalObject q' :=
  conormalObjectIso q q' sourceIso targetIso comm

/-- Two invertible quotients of the same module that determine the same compatible-isomorphism
class have canonically isomorphic conormal objects. -/
def conormalObjectIsoOfMkEq {X : AlgebraicSpace S} {E : X.Modules}
    {q q' : CategoryTheory.InvertibleQuotient E} (h : IsoClass.mk q = IsoClass.mk q') :
    conormalObject q ≅ conormalObject q' :=
  conormalObjectIsoOf q q' (Iso.refl _) (targetIsoOfMkEq h) (targetIsoOfMkEq_spec h)

/-- Module pullback of algebraic spaces preserves zero morphisms. -/
instance preservesZeroMorphisms_modulesPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Modules.pullback f).PreservesZeroMorphisms := sorry

/-- The canonical comparison from the pullback of a quotient kernel to the kernel of the
pulled-back quotient map. -/
def pullbackKernelComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    (Modules.pullback f).obj (kernel q.hom) ⟶ kernel ((pullback f q).hom) :=
  kernelComparison q.hom (Modules.pullback f)

/-- The kernel comparison for a pulled-back invertible quotient, tensored with the identity
on the chosen inverse of the pulled-back target. -/
def pullbackConormalComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    (Modules.pullback f).obj (kernel q.hom) ⊗
        @isInvertibleObject.inverse _ _ _ (pullback f q).object (pullback f q).isInvertible ⟶
      conormalObject (pullback f q) :=
  pullbackKernelComparison f q ⊗ₘ
    𝟙 (@isInvertibleObject.inverse _ _ _ (pullback f q).object (pullback f q).isInvertible)

/-- The kernel-tensor comparison for pulled-back quotient conormal objects is an isomorphism. -/
theorem pullbackConormalComparison_isIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {E : Y.Modules} (q : CategoryTheory.InvertibleQuotient E) :
    IsIso (pullbackConormalComparison f q) := sorry

end InvertibleQuotient
end AlgebraicSpace
end AlgebraicGeometry
