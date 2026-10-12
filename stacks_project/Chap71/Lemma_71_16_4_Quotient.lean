/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.Conormal
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.IsoClass
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

/-- Pullback preserves epimorphic quotient maps of algebraic-space modules. -/
theorem pullbackMap_epi {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    Epi ((Modules.pullback f).map q.hom) := sorry

/-- Pulling back an invertible quotient gives an invertible quotient of the pulled-back
source module. -/
def pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Y.Modules}
    (q : CategoryTheory.InvertibleQuotient E) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback f).obj E) where
  object := (Modules.pullback f).obj q.object
  isInvertible := sorry
  hom := (Modules.pullback f).map q.hom
  hom_epi := pullbackMap_epi f q

/-- Pullback of an invertible quotient target remains invertible. -/
instance instIsInvertible_pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {E : Y.Modules} (q : CategoryTheory.InvertibleQuotient E) :
    isInvertibleObject ((Modules.pullback f).obj q.object) :=
  (pullback f q).isInvertible

/-- Pullback preserves compatible target isomorphisms between invertible quotients. -/
theorem pullback_rel {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Y.Modules}
    {q q' : CategoryTheory.InvertibleQuotient E} (h : Rel q q') :
    Rel (pullback f q) (pullback f q') := sorry

/-- Pullback of invertible quotients descends to compatible-isomorphism classes. -/
def pullbackClass {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Y.Modules} :
    IsoClass E → IsoClass ((Modules.pullback f).obj E) :=
  Quotient.map (pullback f) (fun _ _ ↦ pullback_rel f)

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
