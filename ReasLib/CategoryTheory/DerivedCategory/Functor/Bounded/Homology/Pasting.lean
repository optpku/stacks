/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CatCommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pasting homology comparisons

This file packages the categorical pasting shared by bounded-below,
bounded-above, and bounded homology comparisons. The construction is
independent of complexes, localizations, and boundedness conventions.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory.Functor.HomologyComparison

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {K₀ : Type u₃} [Category.{v₃} K₀]
variable {K : Type u₄} [Category.{v₄} K]
variable {K' : Type u₅} [Category.{v₅} K']
variable {C : Type u₆} [Category.{v₆} C]
variable {D : Type u₇} [Category.{v₇} D]
variable {E : Type u₈} [Category.{v₈} E]
variable {Z : Type u₉} [Category.{v₉} Z]

/-- Paste quotient, bounded-localization, and homology-factor comparisons.

The first square compares mapping before and after a quotient.  The next two
squares compare the bounded quotient and localization with their ambient
counterparts.  The last two isomorphisms identify the ambient localization
and its factored homology functor. -/
@[stacks 015H "pasting localization and homology comparisons"]
def pasteIso
    {M : X ⥤ Y} {S : X ⥤ K₀} {R : Y ⥤ K} {T : K₀ ⥤ K}
    {J : Y ⥤ C} {JK : K ⥤ K'} {R₀ : C ⥤ K'}
    {Qh : K ⥤ D} {I : D ⥤ E} {Qh₀ : K' ⥤ E} {Q : C ⥤ E}
    {Hc : C ⥤ Z} {Hd : E ⥤ Z}
    (mapQuotientSq : CatCommSq M S R T)
    (quotientInclusionSq : CatCommSq R J JK R₀)
    (derivedInclusionSq : CatCommSq Qh JK I Qh₀)
    (ambientLocalizationIso : R₀ ⋙ Qh₀ ≅ Q)
    (factors : Q ⋙ Hd ≅ Hc) :
    (M ⋙ J) ⋙ Hc ≅ (S ⋙ (T ⋙ Qh)) ⋙ (I ⋙ Hd) :=
  Functor.associator M J Hc ≪≫
    (Functor.rightUnitor (M ⋙ (J ⋙ Hc))).symm ≪≫
      (CatCommSq.hComp' mapQuotientSq
        ({ iso :=
            Functor.rightUnitor (J ⋙ Hc) ≪≫
              Functor.isoWhiskerLeft J factors.symm ≪≫
                (CatCommSq.hComp'
                  ({ iso :=
                      (CatCommSq.hComp' quotientInclusionSq
                        derivedInclusionSq).iso ≪≫
                        Functor.isoWhiskerLeft J ambientLocalizationIso } :
                    CatCommSq (R ⋙ Qh) J I Q)
                  ({ iso := Functor.rightUnitor (I ⋙ Hd) } :
                    CatCommSq (I ⋙ Hd) I (𝟭 Z) Hd)).iso.symm ≪≫
                  Functor.rightUnitor ((R ⋙ Qh) ⋙ (I ⋙ Hd)) ≪≫
                    Functor.associator R Qh (I ⋙ Hd) } :
          CatCommSq (J ⋙ Hc) R (𝟭 Z) (Qh ⋙ (I ⋙ Hd)))).iso ≪≫
        Functor.isoWhiskerLeft S
          (Functor.associator T Qh (I ⋙ Hd)).symm ≪≫
      (Functor.associator S (T ⋙ Qh) (I ⋙ Hd)).symm

namespace pasteIso

/-- A pasted homology comparison consists objectwise of the inverse homology
factor, the inverse localization comparison, and the forward quotient
comparison. -/
@[simp, stacks 015H "components of pasted localization-homology comparisons"]
theorem app
    {M : X ⥤ Y} {S : X ⥤ K₀} {R : Y ⥤ K} {T : K₀ ⥤ K}
    {J : Y ⥤ C} {JK : K ⥤ K'} {R₀ : C ⥤ K'}
    {Qh : K ⥤ D} {I : D ⥤ E} {Qh₀ : K' ⥤ E} {Q : C ⥤ E}
    {Hc : C ⥤ Z} {Hd : E ⥤ Z}
    (mapQuotientSq : CatCommSq M S R T)
    (quotientInclusionSq : CatCommSq R J JK R₀)
    (derivedInclusionSq : CatCommSq Qh JK I Qh₀)
    (ambientLocalizationIso : R₀ ⋙ Qh₀ ≅ Q)
    (factors : Q ⋙ Hd ≅ Hc) (x : X) :
    (pasteIso mapQuotientSq quotientInclusionSq derivedInclusionSq
      ambientLocalizationIso factors).app x =
        factors.symm.app (J.obj (M.obj x)) ≪≫
          Hd.mapIso
            (((CatCommSq.hComp' quotientInclusionSq derivedInclusionSq).iso ≪≫
              Functor.isoWhiskerLeft J ambientLocalizationIso).symm.app
                (M.obj x)) ≪≫
          ((Qh ⋙ I) ⋙ Hd).mapIso (mapQuotientSq.iso.app x) := sorry

end pasteIso

end CategoryTheory.Functor.HomologyComparison
