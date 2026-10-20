/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ProEtaleComparison
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

/-!
# Constructible reduction of pro-étale derived complexes

Bounded-above constructibility of reduction modulo an ideal implies the same
property for reduction modulo each natural power of the ideal.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I)))]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I))]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I))]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I)),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]

/-- If a derived pro-étale complex over a Noetherian ring has bounded-above
constructible reduction modulo an ideal, then its reduction modulo every natural
power of that ideal is bounded above and has constructible cohomology. -/
theorem proEtReduction_constructibleProEtaleModule
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (h1 : IsBoundedAbove
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h1c : cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I))
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ n)),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    IsBoundedAbove (proEtReduction I n K) ∧
      cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ n))
        (proEtReduction I n K) :=
  sorry

/-- A derived pro-étale complex whose reduction modulo an ideal is bounded above
and constructible has bounded-above reduction modulo every natural power of that ideal. -/
theorem proEtReduction_constructibleProEtaleModule_isBoundedAbove
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (h1 : IsBoundedAbove
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h1c : cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I))
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ n)),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    IsBoundedAbove (proEtReduction I n K) :=
  (proEtReduction_constructibleProEtaleModule I K h1 h1c n).1

/-- A derived pro-étale complex whose reduction modulo an ideal is bounded above
and constructible has constructible cohomology after reduction modulo every natural
power of that ideal. -/
theorem proEtReduction_constructibleProEtaleModule_cohomologyIn
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (h1 : IsBoundedAbove
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h1c : cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I))
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ n)),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ n))
      (proEtReduction I n K) :=
  (proEtReduction_constructibleProEtaleModule I K h1 h1c n).2

end AlgebraicGeometry.Scheme

end

end
