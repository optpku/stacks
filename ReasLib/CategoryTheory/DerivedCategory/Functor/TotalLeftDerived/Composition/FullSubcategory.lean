/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left.FullSubcategory
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Comparison

@[expose] public section

/-!
# Total Left-Derived Composition from Full-Subcategory Resolutions

This leaf gives a resolution criterion for the canonical comparison between an iterated total
left derived functor and the total left derived functor of the composite.  The hypotheses are
checked only on a full subcategory resolving the source homotopy category.  No invertibility of
the comparison is assumed in the construction.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor.LeftDerived.Homotopy.Composition.FullSubcategory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C]

set_option backward.isDefEq.respectTransparency false in
/-- Stacks 05T2: if a full subcategory resolves the source homotopy category and the three
total-left-derived counits are invertible on the relevant good models, then the canonical
comparison from the iterated model to the model of the composite is invertible. -/
@[stacks 05T2 "total left-derived composition from good-model counits"]
theorem isIso_of_counit
    (F : B ⥤ A) (G : C ⥤ B) (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    (P : ObjectProperty (HomotopyCategory C (up ℤ)))
    [(fullSubcategoryLocalizerMorphism P
      (HomotopyCategory.quasiIso C (up ℤ))).HasLeftResolutions]
    (hG : ∀ K, P K → IsIso ((LeftDerived.Homotopy.counit G).app K))
    (hF : ∀ K, P K → IsIso ((LeftDerived.Homotopy.counit F).app
      ((G.mapHomotopyCategory (up ℤ)).obj K)))
    (hH : ∀ K, P K → IsIso ((LeftDerived.Homotopy.counit H).app K)) :
    IsIso (Functor.LeftDerived.Homotopy.Composition.comparison F G H hcomp) := by
  rw [(fullSubcategoryLocalizerMorphism P
    (HomotopyCategory.quasiIso C (up ℤ))).isIso_iff_of_hasLeftResolutions
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)]
  intro K
  letI := hG K.obj K.property
  letI := hF K.obj K.property
  haveI : IsIso ((Functor.LeftDerived.Homotopy.Composition.counit F G).app K.obj) := by
    change IsIso ((Functor.LeftDerived.Composition.iteratedCounit
      (LeftDerived.Homotopy.counit G) (LeftDerived.Homotopy.counit F)).app K.obj)
    rw [Functor.LeftDerived.Composition.iteratedCounit_app]
    infer_instance
  letI := hH K.obj K.property
  exact IsIso.of_isIso_fac_right
    (Functor.LeftDerived.Homotopy.Composition.comparison_fac_app F G H hcomp K.obj)

/-- Stacks 05T2: a resolving full subcategory on which the first functor, the second functor at
the image models, and their composite are computed by the underived functors makes the canonical
total-left-derived composition comparison invertible. -/
@[stacks 05T2 "total left-derived composition from computing models"]
theorem isIso
    (F : B ⥤ A) (G : C ⥤ B) (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    (P : ObjectProperty (HomotopyCategory C (up ℤ)))
    [(fullSubcategoryLocalizerMorphism P
      (HomotopyCategory.quasiIso C (up ℤ))).HasLeftResolutions]
    (hG : ∀ K, P K → LeftDerived.ComputesAt
      (Functor.Homotopy.toDerived G) (HomotopyCategory.quasiIso C (up ℤ)) K)
    (hF : ∀ K, P K → LeftDerived.ComputesAt
      (Functor.Homotopy.toDerived F) (HomotopyCategory.quasiIso B (up ℤ))
        ((G.mapHomotopyCategory (up ℤ)).obj K))
    (hH : ∀ K, P K → LeftDerived.ComputesAt
      (Functor.Homotopy.toDerived H) (HomotopyCategory.quasiIso C (up ℤ)) K) :
    IsIso (Functor.LeftDerived.Homotopy.Composition.comparison F G H hcomp) := by
  apply isIso_of_counit F G H hcomp P
  · intro K hK
    exact LeftDerived.ComputesAt.isIso_app
      (Functor.Homotopy.toDerived G) (HomotopyCategory.quasiIso C (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
      (LeftDerived.Homotopy.functor G) (LeftDerived.Homotopy.counit G) K
      (hG K hK) inferInstance
  · intro K hK
    exact LeftDerived.ComputesAt.isIso_app
      (Functor.Homotopy.toDerived F) (HomotopyCategory.quasiIso B (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B)
      (LeftDerived.Homotopy.functor F) (LeftDerived.Homotopy.counit F)
      ((G.mapHomotopyCategory (up ℤ)).obj K) (hF K hK) inferInstance
  · intro K hK
    exact LeftDerived.ComputesAt.isIso_app
      (Functor.Homotopy.toDerived H) (HomotopyCategory.quasiIso C (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
      (LeftDerived.Homotopy.functor H) (LeftDerived.Homotopy.counit H) K
      (hH K hK) inferInstance

end CategoryTheory.Functor.LeftDerived.Homotopy.Composition.FullSubcategory
