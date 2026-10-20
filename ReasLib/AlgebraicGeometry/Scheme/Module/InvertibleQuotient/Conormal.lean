/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.InvertibleQuotient.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.Conormal

/-!
# Pullback of conormal objects of invertible quotients

This file gives the canonical kernel and tensor-inverse comparisons relating
the conormal object of an invertible quotient to that of its pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory.InvertibleQuotient

variable {X Y Z : Scheme.{u}}

/-- The canonical comparison from the pullback of a quotient kernel to the kernel of the
pulled-back quotient map. -/
noncomputable def pullbackKernelComparison (f : X ⟶ Y) {E : Y.Modules}
    (q : InvertibleQuotient E) :
    (Scheme.Modules.pullback f).obj (kernel q.hom) ⟶
      kernel ((pullback f q).hom) :=
  kernelComparison q.hom (Scheme.Modules.pullback f)

/-- Pullback identifies the kernel of an epimorphic quotient with the kernel of its pulled-back
quotient map. -/
theorem pullbackKernelComparison_isIso (f : X ⟶ Y) {E : Y.Modules}
    (q : InvertibleQuotient E) :
    IsIso (pullbackKernelComparison f q) := sorry

/-- The canonical comparison from the pullback of a quotient conormal object to the conormal
object of the pulled-back quotient. -/
noncomputable def pullbackConormalComparison (f : X ⟶ Y) {E : Y.Modules}
    (q : InvertibleQuotient E) :
    (Scheme.Modules.pullback f).obj (conormalObject q) ⟶
      conormalObject (pullback f q) :=
  Scheme.Modules.pullbackTensorComparison f (kernel q.hom)
      (@isInvertibleObject.inverse Y.Modules _ _ q.object q.isInvertible) ≫
    (pullbackKernelComparison f q ⊗ₘ
      (@isInvertibleObject.mapInverseIso Y.Modules _ _ X.Modules _ _
        (Scheme.Modules.pullback f)
          (AlgebraicGeometry.Scheme.Modules.pullbackMonoidal f)
          q.object q.isInvertible).inv)

/-- The pullback comparison for quotient conormal objects is an isomorphism. -/
theorem pullbackConormalComparison_isIso (f : X ⟶ Y) {E : Y.Modules}
    (q : InvertibleQuotient E) :
    IsIso (pullbackConormalComparison f q) := sorry

/-- The conormal comparison for identity pullback is compatible with the canonical
pullback-identity transport. -/
theorem pullbackConormalComparison_id {E : X.Modules}
    (q : InvertibleQuotient E) :
    pullbackConormalComparison (𝟙 X) q ≫
        (conormalObjectIso (pullback (𝟙 X) q) q
          ((Scheme.Modules.pullbackId X).app E)
          ((Scheme.Modules.pullbackId X).app q.object)
          (by simpa [pullback] using
            (Scheme.Modules.pullbackId X).hom.naturality q.hom)).hom =
      (Scheme.Modules.pullbackId X).hom.app (conormalObject q) := sorry

/-- Conormal comparison along a composite is compatible with the two successive pullback
comparisons. -/
theorem pullbackConormalComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {E : Z.Modules} (q : InvertibleQuotient E) :
    pullbackConormalComparison (f ≫ g) q =
      (Scheme.Modules.pullbackComp f g).inv.app (conormalObject q) ≫
        (Scheme.Modules.pullback f).map (pullbackConormalComparison g q) ≫
          pullbackConormalComparison f (pullback g q) ≫
            (conormalObjectIso (pullback f (pullback g q)) (pullback (f ≫ g) q)
              ((Scheme.Modules.pullbackComp f g).app E)
              ((Scheme.Modules.pullbackComp f g).app q.object)
              (by
                change (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).map q.hom ≫
                    (Scheme.Modules.pullbackComp f g).hom.app q.object =
                  (Scheme.Modules.pullbackComp f g).hom.app E ≫
                    (Scheme.Modules.pullback (f ≫ g)).map q.hom
                exact (Scheme.Modules.pullbackComp f g).hom.naturality q.hom)).hom := sorry

end CategoryTheory.InvertibleQuotient
