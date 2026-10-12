/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Inverse.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison counit construction

This module constructs the counit isomorphism for the explicit inverse of the
relative-inertia comparison. Component computations live in
`DiagonalComparison.Counit.Computations`.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The base isomorphism used by the counit for the explicit comparison inverse. It is induced
by the fiber-membership equality already stored in the target self-pullback object. -/
@[stacks 034H "diagonal-comparison counit base isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.counitIso.app.baseIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.baseObj
        ((RelativeInertia.diagonalComparison.inverse F ⋙
          RelativeInertia.diagonalComparison F).obj P) ≅
      PseudoPullback.baseObj P :=
  PseudoPullback.fstBaseIso P

/-- The first-component isomorphism used by the counit for the explicit comparison inverse is
the identity on the selected first object. -/
@[stacks 034H "diagonal-comparison counit first-component isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.counitIso.app.fstIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstObj
        ((RelativeInertia.diagonalComparison.inverse F ⋙
          RelativeInertia.diagonalComparison F).obj P) ≅
      PseudoPullback.fstObj P :=
  Iso.refl _

/-- The second-component isomorphism used by the counit for the explicit comparison inverse is
the second component of the target object's structural isomorphism. -/
@[stacks 034H "diagonal-comparison counit second-component isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.counitIso.app.sndIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.sndObj
        ((RelativeInertia.diagonalComparison.inverse F ⋙
          RelativeInertia.diagonalComparison F).obj P) ≅
      PseudoPullback.sndObj P :=
  RelativeInertia.diagonalComparison.inverse.sndIso F P

/-- The forward first-component counit isomorphism lies over the forward base isomorphism. -/
@[stacks 034H "diagonal-comparison counit first-component hom-lift"]
theorem RelativeInertia.diagonalComparison.counitIso.app.fstIso.hom.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    X.p.IsHomLift
      (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P).hom
      (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P).hom := sorry

/-- The forward second-component counit isomorphism lies over the forward base isomorphism. -/
@[stacks 034H "diagonal-comparison counit second-component hom-lift"]
theorem RelativeInertia.diagonalComparison.counitIso.app.sndIso.hom.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    X.p.IsHomLift
      (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P).hom
      (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P).hom := sorry

/-- The component isomorphisms of the explicit comparison counit respect the two structural
comparisons in the outer self-pullback. -/
@[stacks 034H "diagonal-comparison counit component compatibility"]
theorem RelativeInertia.diagonalComparison.counitIso.app.w (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    CommSq
      ((relativeDiagonal F).map
        (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P).hom)
      (PseudoPullback.comparison
        ((RelativeInertia.diagonalComparison.inverse F ⋙
          RelativeInertia.diagonalComparison F).obj P))
      (PseudoPullback.comparison P)
      ((relativeDiagonal F).map
        (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P).hom) := sorry

/-- The component of the counit identifying comparison after the explicit inverse with the
original self-pullback object. -/
@[stacks 034H "diagonal-comparison counit component"]
noncomputable def RelativeInertia.diagonalComparison.counitIso.app (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse F ⋙
        RelativeInertia.diagonalComparison F).obj P ≅ P :=
  PseudoPullback.mkIso
    (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P)
    (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P)
    (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P)
    (hom_fst := RelativeInertia.diagonalComparison.counitIso.app.fstIso.hom.isHomLift F P)
    (hom_snd := RelativeInertia.diagonalComparison.counitIso.app.sndIso.hom.isHomLift F P)
    (RelativeInertia.diagonalComparison.counitIso.app.w F P)

/-- The explicit comparison counit components are natural in self-pullback morphisms. -/
@[stacks 034H "diagonal-comparison counit naturality"]
theorem RelativeInertia.diagonalComparison.counitIso.naturality (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    (RelativeInertia.diagonalComparison.inverse F ⋙
        RelativeInertia.diagonalComparison F).map φ ≫
        (RelativeInertia.diagonalComparison.counitIso.app F Q).hom =
      (RelativeInertia.diagonalComparison.counitIso.app F P).hom ≫ φ := sorry

/-- The inverse comparison-counit component is natural in self-pullback morphisms. -/
@[reassoc, stacks 034H "diagonal-comparison inverse counit naturality"]
theorem RelativeInertia.diagonalComparison.counitIso.invNaturality (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    (RelativeInertia.diagonalComparison.counitIso.app F P).inv ≫
        (RelativeInertia.diagonalComparison.inverse F ⋙
          RelativeInertia.diagonalComparison F).map φ =
      φ ≫ (RelativeInertia.diagonalComparison.counitIso.app F Q).inv := sorry

/-- The ordinary natural isomorphism underlying the counit for the explicit comparison
inverse. -/
@[stacks 034H "diagonal-comparison counit underlying natural isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.counitIso.toNatIso (F : X ⥤ᵇ Y) :
    (RelativeInertia.diagonalComparison.inverse F ⋙
        RelativeInertia.diagonalComparison F).toFunctor ≅
      (𝟭 (PseudoPullback (relativeDiagonal F) (relativeDiagonal F))).toFunctor :=
  NatIso.ofComponents
    (RelativeInertia.diagonalComparison.counitIso.app F)
    (fun φ ↦ RelativeInertia.diagonalComparison.counitIso.naturality F φ)

/-- Every forward explicit comparison counit component is vertical over the identity of its
base object. -/
@[stacks 034H "diagonal-comparison counit forward hom-lift"]
theorem RelativeInertia.diagonalComparison.counitIso.app.hom.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.IsHomLift
      (𝟙 ((PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.obj P))
      (RelativeInertia.diagonalComparison.counitIso.app F P).hom := sorry

/-- Every inverse comparison-counit component is vertical over the identity of its base object. -/
@[stacks 034H "diagonal-comparison counit inverse hom-lift"]
theorem RelativeInertia.diagonalComparison.counitIso.app.inv.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.IsHomLift
      (𝟙 ((PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.obj P))
      (RelativeInertia.diagonalComparison.counitIso.app F P).inv := sorry

/-- The based natural isomorphism serving as the counit for the explicit relative-inertia
comparison inverse. -/
@[stacks 034H "relative-inertia diagonal-comparison counit"]
noncomputable def RelativeInertia.diagonalComparison.counitIso (F : X ⥤ᵇ Y) :
    RelativeInertia.diagonalComparison.inverse F ⋙
        RelativeInertia.diagonalComparison F ≅
      𝟭 (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)) :=
  BasedNatIso.mkNatIso
    (RelativeInertia.diagonalComparison.counitIso.toNatIso F)
    (RelativeInertia.diagonalComparison.counitIso.app.hom.isHomLift F)

end BasedFunctor

end CategoryTheory
