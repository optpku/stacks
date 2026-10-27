/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleQuotient.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Kernel
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Inverse
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.Conormal

/-! # Conormal objects of invertible quotients under base change -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalCategory.isInvertibleObject
open CategoryTheory.InvertibleQuotient

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient

variable {S : Scheme.{u}}

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

/-- Canonical comparison from the pullback of a quotient conormal object to the conormal object
of the pulled-back quotient. -/
def pullbackConormalObjectComparison {Y Z : AlgebraicSpace S} (h : Y ⟶ Z)
    {E : Z.Modules} (q : InvertibleQuotient E) :
    (Modules.pullback h).obj (conormalObject q) ⟶
      conormalObject (AlgebraicSpace.InvertibleQuotient.pullback h q) :=
  RelativeProj.pullbackTensorOplax h (kernel q.hom)
      (@isInvertibleObject.inverse _ _ _ q.object q.isInvertible) ≫
    (kernelComparison q.hom (Modules.pullback h) ⊗ₘ
      @Modules.PullbackTensor.inverseComparison S Y Z h q.object q.isInvertible
        (AlgebraicSpace.InvertibleQuotient.pullback h q).isInvertible)

/-- The pullback comparison on conormal objects is an isomorphism. -/
theorem pullbackConormalObjectComparison_isIso {Y Z : AlgebraicSpace S}
    (h : Y ⟶ Z) {E : Z.Modules} (q : InvertibleQuotient E) :
    IsIso (pullbackConormalObjectComparison h q) := sorry

/-- The kernel tensored with the inverse target of an invertible quotient of a
quasi-coherent module is quasi-coherent. -/
theorem conormalObject_isQuasicoherent {X : AlgebraicSpace S} {E : X.Modules}
    [E.IsQuasicoherent] (q : CategoryTheory.InvertibleQuotient E) :
    (conormalObject q).IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient
