/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.PNat.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import stacks_project.Chap61.Lemma_61_19_11_Reduction
public import stacks_project.Chap61.Lemma_61_27_2_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.27.6

If the reduction `K_1` of `K` in `D(X.ProEt, Λ)` lies in `D_c^-(X.ProEt, Λ ⧸ I)`,
then every positive-power reduction `K_n` lies in `D_c^-(X.ProEt, Λ ⧸ I ^ n)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I))]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} (Λ ⧸ I))]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I)),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]

/-- Lemma 61.27.6: for a scheme `X`, a Noetherian ring `Λ`, an ideal `I ⊆ Λ`,
and `K` in `D(X.ProEt, Λ)`, writing `K_n` for the derived reduction
`proEtReduction I n K` (the object `K ⊗^L underline(Λ ⧸ I ^ n)` of
`D(X.ProEt, Λ ⧸ I ^ n)`), if `K_1` lies in `D_c^-(X.ProEt, Λ ⧸ I)`, then
every positive-power reduction `K_n` lies in `D_c^-(X.ProEt, Λ ⧸ I ^ n)`. -/
@[stacks 09BR]
theorem proEtReduction_constructibleProEtaleModule
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (h1 : IsBoundedAbove
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h1c : cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I))
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (n : ℕ+)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    IsBoundedAbove (proEtReduction I n K) ∧
      cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ (n : ℕ)))
        (proEtReduction I n K) :=
  sorry

/-- The reduction `proEtReduction I n K` is bounded above. -/
theorem proEtReduction_constructibleProEtaleModule_isBoundedAbove
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (h1 : IsBoundedAbove
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h1c : cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I))
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (n : ℕ+)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    IsBoundedAbove (proEtReduction I n K) :=
  sorry

/-- The reduction `proEtReduction I n K` has constructible cohomology sheaves. -/
theorem proEtReduction_constructibleProEtaleModule_cohomologyIn
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (h1 : IsBoundedAbove
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h1c : cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I))
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (n : ℕ+)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ (n : ℕ)))
      (proEtReduction I n K) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
