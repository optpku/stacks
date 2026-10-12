/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections.Comparison
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections.Construction

/-!
# Computations for locally induced two-fibre-product projections

These lemmas expose the component and both directions of the naturality comparison of the
canonical projection strong transformations.
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

/-- The object component of the canonical first-projection transformation is the explicit
locally induced first projection. -/
@[simp]
theorem pseudofunctor.fst.app
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor.fst P Q).app S =
      _root_.CategoryTheory.LocallyInduced.TwoFibreProduct.fst S.fst S.snd := sorry

/-- Naturality of the canonical first-projection transformation is the explicit first
projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor.fst P Q).naturality ψ = pseudofunctor.fstIso ψ := sorry

/-- The forward naturality cell of the first-projection transformation is the forward explicit
first-projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality.hom
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.fst P Q).naturality ψ).hom =
      (pseudofunctor.fstIso ψ).hom := sorry

/-- The inverse naturality cell of the first-projection transformation is the inverse explicit
first-projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality.inv
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.fst P Q).naturality ψ).inv =
      (pseudofunctor.fstIso ψ).inv := sorry

/-- The object component of the canonical second-projection transformation is the explicit
locally induced second projection. -/
@[simp]
theorem pseudofunctor.snd.app
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor.snd P Q).app S =
      _root_.CategoryTheory.LocallyInduced.TwoFibreProduct.snd S.fst S.snd := sorry

/-- Naturality of the canonical second-projection transformation is the explicit second
projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor.snd P Q).naturality ψ = pseudofunctor.sndIso ψ := sorry

/-- The forward naturality cell of the second-projection transformation is the forward explicit
second-projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality.hom
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.snd P Q).naturality ψ).hom =
      (pseudofunctor.sndIso ψ).hom := sorry

/-- The inverse naturality cell of the second-projection transformation is the inverse explicit
second-projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality.inv
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.snd P Q).naturality ψ).inv =
      (pseudofunctor.sndIso ψ).inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
