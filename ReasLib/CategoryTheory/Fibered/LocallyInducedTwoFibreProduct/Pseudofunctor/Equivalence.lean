module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences induced by the locally induced two-fibre-product pseudofunctor

This leaf exposes the apex-facing equivalence and its four structural components. The generic
`Pseudofunctor.mapEquivalence` construction remains the data owner.
-/

@[expose] public section

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

/-- A bicategorical equivalence of bundled selected cospans induces the canonical equivalence
of their explicit locally induced two-fibre-product apices. -/
@[stacks 02XQ "equivalence of locally induced two-fibre-products"]
def pseudofunctor.mapEquivalence
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (e : S ≌ T) :
    apex S.fst S.snd ≌ apex T.fst T.snd :=
  (pseudofunctor P Q).mapEquivalence e

/-- The forward morphism of the induced equivalence is the explicit map of the forward
cospan transformation. -/
@[simp]
theorem pseudofunctor.mapEquivalence.hom
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).hom =
      _root_.CategoryTheory.LocallyInduced.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform e.hom) := sorry

/-- The inverse morphism of the induced equivalence is the explicit map of the inverse
cospan transformation. -/
@[simp]
theorem pseudofunctor.mapEquivalence.inv
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).inv =
      _root_.CategoryTheory.LocallyInduced.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform e.inv) := sorry

/-- The unit of the induced equivalence is the canonical pseudofunctorial unit. -/
@[simp]
theorem pseudofunctor.mapEquivalence.unit
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor P Q) e := sorry

/-- The counit of the induced equivalence is the canonical pseudofunctorial counit. -/
@[simp]
theorem pseudofunctor.mapEquivalence.counit
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).counit =
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor P Q) e := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
