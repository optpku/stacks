/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Normalized
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Quotient.Fppf

/-!
# Fppf comparison of relative quotient and section-normalized classes

Sheafification carries the natural quotient/kernel comparison to a natural
isomorphism of additive fppf sheaves. Only a section is needed. This comparison
does not use the separate raw/quotient local-triviality proof obligation.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

/-- The quotient fppf sheaf has the section-normalized presentation. -/
noncomputable def quotientNormalizedFppfIso {S : Scheme.{u}} (X : Over S)
    (P : 𝟙_ (Over S) ⟶ X) :
    quotientFppfSheaf X ≅
      (plusPlusSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
        (normalizedPresheaf X P) :=
  (plusPlusSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).mapIso
    (quotientNormalizedIso X P)

end AlgebraicGeometry.RelativePicard
