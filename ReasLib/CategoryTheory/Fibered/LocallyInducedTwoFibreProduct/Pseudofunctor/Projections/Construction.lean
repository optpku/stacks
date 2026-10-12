/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.StrongTrans.LiftTo
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections.Ambient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for locally induced two-fibre products

The ambient projections satisfy the selected hom property and therefore lift canonically to
strong transformations valued in the locally induced bicategory.
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

/-- The first ambient projection component satisfies the selected hom property. -/
private theorem pseudofunctor.fst.ambient.app_mem
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    Q ((pseudofunctor.ambient (P := P) (Q := Q)).obj S) S.left
      ((pseudofunctor.fst.ambient P Q).app S).hom := sorry

/-- The second ambient projection component satisfies the selected hom property. -/
private theorem pseudofunctor.snd.ambient.app_mem
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    Q ((pseudofunctor.ambient (P := P) (Q := Q)).obj S) S.right
      ((pseudofunctor.snd.ambient P Q).app S).hom := sorry

variable (P Q) in
/-- The canonical first projection from the locally induced two-fibre-product pseudofunctor
to the left-endpoint projection on bundled selected cospans. -/
@[stacks 02XQ "first projection strong transformation for locally induced two-fibre-products"]
def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor P Q)
      (Bicategory.Cospan.leftProjection
        (Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q)) :=
  Bicategory.LocallyInducedBicategory.StrongTrans.liftTo
    (Q := Q)
    (pseudofunctor.ambient (P := P) (Q := Q))
    (Bicategory.Cospan.leftProjection
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    (pseudofunctor.ambient.map_mem (P := P) (Q := Q))
    (pseudofunctor.fst.ambient P Q)
    pseudofunctor.fst.ambient.app_mem

variable (P Q) in
/-- The canonical second projection from the locally induced two-fibre-product pseudofunctor
to the right-endpoint projection on bundled selected cospans. -/
@[stacks 02XQ "second projection strong transformation for locally induced two-fibre-products"]
def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor P Q)
      (Bicategory.Cospan.rightProjection
        (Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q)) :=
  Bicategory.LocallyInducedBicategory.StrongTrans.liftTo
    (Q := Q)
    (pseudofunctor.ambient (P := P) (Q := Q))
    (Bicategory.Cospan.rightProjection
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    (pseudofunctor.ambient.map_mem (P := P) (Q := Q))
    (pseudofunctor.snd.ambient P Q)
    pseudofunctor.snd.ambient.app_mem

end LocallyInduced.TwoFibreProduct

end CategoryTheory
