/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Projections.Construction

/-!
# Computations for explicit pseudo-pullback projection transformations

Objectwise comparison formulas and direct readouts of both canonical strong transformations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The forward component of the bundled first-projection comparison is the explicit
objectwise comparison. -/
@[simp]
theorem pseudofunctor.fstIso.hom.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    (pseudofunctor.fstIso ψ).hom.toNatTrans.app P =
      (map.fstComponent (Bicategory.Cospan.Hom.toBasedTransform ψ) P).hom := sorry

/-- The inverse component of the bundled first-projection comparison is the inverse explicit
objectwise comparison. -/
@[simp]
theorem pseudofunctor.fstIso.inv.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    (pseudofunctor.fstIso ψ).inv.toNatTrans.app P =
      (map.fstComponent (Bicategory.Cospan.Hom.toBasedTransform ψ) P).inv := sorry

/-- Every forward first-projection comparison component is vertical over the identity on the
common base object. -/
theorem pseudofunctor.fstIso.hom.app.isHomLift
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    T.left.p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      ((pseudofunctor.fstIso ψ).hom.toNatTrans.app P) := sorry

/-- Every inverse first-projection comparison component is vertical over the identity on the
common base object. -/
theorem pseudofunctor.fstIso.inv.app.isHomLift
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    T.left.p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      ((pseudofunctor.fstIso ψ).inv.toNatTrans.app P) := sorry

/-- The forward component of the bundled second-projection comparison is the explicit
objectwise comparison. -/
@[simp]
theorem pseudofunctor.sndIso.hom.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    (pseudofunctor.sndIso ψ).hom.toNatTrans.app P =
      (map.sndComponent (Bicategory.Cospan.Hom.toBasedTransform ψ) P).hom := sorry

/-- The inverse component of the bundled second-projection comparison is the inverse explicit
objectwise comparison. -/
@[simp]
theorem pseudofunctor.sndIso.inv.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    (pseudofunctor.sndIso ψ).inv.toNatTrans.app P =
      (map.sndComponent (Bicategory.Cospan.Hom.toBasedTransform ψ) P).inv := sorry

/-- Every forward second-projection comparison component is vertical over the identity on the
common base object. -/
theorem pseudofunctor.sndIso.hom.app.isHomLift
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    T.right.p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      ((pseudofunctor.sndIso ψ).hom.toNatTrans.app P) := sorry

/-- Every inverse second-projection comparison component is vertical over the identity on the
common base object. -/
theorem pseudofunctor.sndIso.inv.app.isHomLift
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    T.right.p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      ((pseudofunctor.sndIso ψ).inv.toNatTrans.app P) := sorry

/-- The object component of the canonical first-projection strong transformation is the
explicit first projection. -/
@[simp]
theorem pseudofunctor.fst.app
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor.fst C).app S =
      _root_.CategoryTheory.BasedCategory.PseudoPullback.fst S.fst S.snd := sorry

/-- The naturality isomorphism of the canonical first-projection strong transformation is
the explicit first-projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) :
    (pseudofunctor.fst C).naturality psi = pseudofunctor.fstIso psi := sorry

/-- The forward naturality cell of the canonical first projection is the forward comparison
cell. -/
@[simp]
theorem pseudofunctor.fst.naturality.hom
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) :
    ((pseudofunctor.fst C).naturality psi).hom =
      (pseudofunctor.fstIso psi).hom := sorry

/-- The inverse naturality cell of the canonical first projection is the inverse comparison
cell. -/
@[simp]
theorem pseudofunctor.fst.naturality.inv
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) :
    ((pseudofunctor.fst C).naturality psi).inv =
      (pseudofunctor.fstIso psi).inv := sorry

/-- The forward naturality component of the canonical first projection is the explicit
objectwise first-projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality.hom.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor.fst C).naturality psi).hom.toNatTrans.app P =
      (map.fstComponent (Bicategory.Cospan.Hom.toBasedTransform psi) P).hom := sorry

/-- The inverse naturality component of the canonical first projection is the inverse
objectwise first-projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality.inv.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor.fst C).naturality psi).inv.toNatTrans.app P =
      (map.fstComponent (Bicategory.Cospan.Hom.toBasedTransform psi) P).inv := sorry

/-- The object component of the canonical second-projection strong transformation is the
explicit second projection. -/
@[simp]
theorem pseudofunctor.snd.app
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor.snd C).app S =
      _root_.CategoryTheory.BasedCategory.PseudoPullback.snd S.fst S.snd := sorry

/-- The naturality isomorphism of the canonical second-projection strong transformation is
the explicit second-projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) :
    (pseudofunctor.snd C).naturality psi = pseudofunctor.sndIso psi := sorry

/-- The forward naturality cell of the canonical second projection is the forward comparison
cell. -/
@[simp]
theorem pseudofunctor.snd.naturality.hom
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) :
    ((pseudofunctor.snd C).naturality psi).hom =
      (pseudofunctor.sndIso psi).hom := sorry

/-- The inverse naturality cell of the canonical second projection is the inverse comparison
cell. -/
@[simp]
theorem pseudofunctor.snd.naturality.inv
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) :
    ((pseudofunctor.snd C).naturality psi).inv =
      (pseudofunctor.sndIso psi).inv := sorry

/-- The forward naturality component of the canonical second projection is the explicit
objectwise second-projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality.hom.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor.snd C).naturality psi).hom.toNatTrans.app P =
      (map.sndComponent (Bicategory.Cospan.Hom.toBasedTransform psi) P).hom := sorry

/-- The inverse naturality component of the canonical second projection is the inverse
objectwise second-projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality.inv.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (psi : S ⟶ T) (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor.snd C).naturality psi).inv.toNatTrans.app P =
      (map.sndComponent (Bicategory.Cospan.Hom.toBasedTransform psi) P).inv := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
