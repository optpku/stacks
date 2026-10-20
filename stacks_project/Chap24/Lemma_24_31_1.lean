/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Algebra.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v uX vX

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable (A : DGA(𝒪)) (Astage : ℕ → DGA(𝒪))
variable (i : ∀ n, Astage n ⟶ Astage (n + 1))
variable (e : A.toComplex ≅ colimit (Functor.ofSequence i ⋙ forgetToComplex))
variable (hstage : ∀ n,
  HomologicalComplex.KFlat.termwiseFlat (up ℤ) (Astage n).toComplex)

/- Lemma 24.31.1 (tag 0FU1): the same sequential-colimit algebra has a K-flat underlying
complex with flat terms after every arbitrary `RingedSite.ToposHom` pullback between
commutative ringed-topos presentations.  Only the underlying complex is pulled back, so no DGA
pullback structure is needed for this assertion. -/
@[stacks 0FU1 "universal ringed-topos pullback"]
#check
  (universallyTermwiseFlat_of_sequence A Astage i e hstage :
    RingedSite.ToposHom.modulePullbackComplex.UniversallyTermwiseFlat.{uX, vX}
      A.toComplex)

/- Before pullback, exact sequential-colimit closure is owned at the underlying-complex level. -/
#check
  (termwiseFlat_of_sequence A Astage i e hstage :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) A.toComplex)

end


end SheafOfModules.RingedSite.DifferentialGradedAlgebra
