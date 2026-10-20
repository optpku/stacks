/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition.Associativity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Projections

/-!
# Ambient projection transformations for locally induced two-fibre products

The transformations in this file are built by composing the explicit pseudo-pullback
projections with the generic endpoint comparisons for `Cospan.map`, then lifting through the
selected full subbicategory. They are the ambient data used by the final locally induced lift.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [Projections.Has (P := P) (Q := Q)]
variable [Q.IsClosedUnderIsomorphisms]
variable [Projections.IsDetected (P := P) (Q := Q)]

variable (P Q) in
/-- Before restoring the object and hom properties, the canonical first projection is the
precomposed explicit pseudo-pullback projection followed by the generic left-endpoint
comparison for `Cospan.map`. -/
def pseudofunctor.fst.ambientBase :
    Pseudofunctor.StrongTrans
      (pseudofunctor.ambientBase (P := P) (Q := Q))
      ((Bicategory.Cospan.leftProjection
          (Bicategory.LocallyInducedBicategory
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)
            (fun X : P.FullSubbicategory ↦ X.1) Q)).comp
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((BasedCategory.PseudoPullback.pseudofunctor.fst C).precomp
      (Bicategory.Cospan.map
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor))
    (Bicategory.Cospan.map.leftProjection
      (Bicategory.LocallyInducedBicategory.forget
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor)

variable (P Q) in
/-- Before restoring the object and hom properties, the canonical second projection is the
precomposed explicit pseudo-pullback projection followed by the generic right-endpoint
comparison for `Cospan.map`. -/
def pseudofunctor.snd.ambientBase :
    Pseudofunctor.StrongTrans
      (pseudofunctor.ambientBase (P := P) (Q := Q))
      ((Bicategory.Cospan.rightProjection
          (Bicategory.LocallyInducedBicategory
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)
            (fun X : P.FullSubbicategory ↦ X.1) Q)).comp
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((BasedCategory.PseudoPullback.pseudofunctor.snd C).precomp
      (Bicategory.Cospan.map
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor))
    (Bicategory.Cospan.map.rightProjection
      (Bicategory.LocallyInducedBicategory.forget
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor)

variable (P Q) in
/-- After restoring the selected object property, the first ambient projection targets the
left-endpoint projection followed by the canonical locally induced inclusion. -/
def pseudofunctor.fst.ambient :
    Pseudofunctor.StrongTrans
      (pseudofunctor.ambient (P := P) (Q := Q))
      ((Bicategory.Cospan.leftProjection
          (Bicategory.LocallyInducedBicategory
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)
            (fun X : P.FullSubbicategory ↦ X.1) Q)).comp
        (Bicategory.LocallyInducedBicategory.ι
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (pseudofunctor.ambientBase (P := P) (Q := Q))
    ((Bicategory.Cospan.leftProjection
        (Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q)).comp
      (Bicategory.LocallyInducedBicategory.ι
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor)
    (pseudofunctor.ambientBase.obj_mem (P := P) (Q := Q))
    (Pseudofunctor.StrongTrans.vcomp
      (pseudofunctor.fst.ambientBase P Q)
      (Pseudofunctor.compAssoc
        (Bicategory.Cospan.leftProjection
          (Bicategory.LocallyInducedBicategory
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)
            (fun X : P.FullSubbicategory ↦ X.1) Q))
        (Bicategory.LocallyInducedBicategory.ι
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor
        (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor).inv)

variable (P Q) in
/-- After restoring the selected object property, the second ambient projection targets the
right-endpoint projection followed by the canonical locally induced inclusion. -/
def pseudofunctor.snd.ambient :
    Pseudofunctor.StrongTrans
      (pseudofunctor.ambient (P := P) (Q := Q))
      ((Bicategory.Cospan.rightProjection
          (Bicategory.LocallyInducedBicategory
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)
            (fun X : P.FullSubbicategory ↦ X.1) Q)).comp
        (Bicategory.LocallyInducedBicategory.ι
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (pseudofunctor.ambientBase (P := P) (Q := Q))
    ((Bicategory.Cospan.rightProjection
        (Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q)).comp
      (Bicategory.LocallyInducedBicategory.ι
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor)
    (pseudofunctor.ambientBase.obj_mem (P := P) (Q := Q))
    (Pseudofunctor.StrongTrans.vcomp
      (pseudofunctor.snd.ambientBase P Q)
      (Pseudofunctor.compAssoc
        (Bicategory.Cospan.rightProjection
          (Bicategory.LocallyInducedBicategory
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)
            (fun X : P.FullSubbicategory ↦ X.1) Q))
        (Bicategory.LocallyInducedBicategory.ι
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor
        (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor).inv)

end LocallyInduced.TwoFibreProduct

end CategoryTheory
