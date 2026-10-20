/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Derived.ConstructibleReduction
import StacksCheckRecall

/-!
# Lemma 61.27.6

Bounded-above constructibility of reduction modulo an ideal implies the same
property for reduction modulo every natural power of that ideal.
-/

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u w

/- Lemma 61.27.6
For a scheme, a Noetherian coefficient ring, an ideal, and a derived pro-étale
complex, bounded-above constructibility modulo the ideal implies bounded-above
constructibility modulo every natural power of the ideal. -/
@[stacks 09BR] #check (AlgebraicGeometry.Scheme.proEtReduction_constructibleProEtaleModule :
  ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I)))]
    [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I)),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]
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
      (ProEt.baseChange f).op.HasLeftKanExtension P],
    IsBoundedAbove (proEtReduction I n K) ∧
      cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ n))
        (proEtReduction I n K))

#check (AlgebraicGeometry.Scheme.proEtReduction_constructibleProEtaleModule_isBoundedAbove :
  ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I)))]
    [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I)),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]
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
      (ProEt.baseChange f).op.HasLeftKanExtension P],
    IsBoundedAbove (proEtReduction I n K))

#check (AlgebraicGeometry.Scheme.proEtReduction_constructibleProEtaleModule_cohomologyIn :
  ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    (I : Ideal Λ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I)))]
    [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I)),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (up ℤ))]
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
      (ProEt.baseChange f).op.HasLeftKanExtension P],
    cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ n))
      (proEtReduction I n K))

end
