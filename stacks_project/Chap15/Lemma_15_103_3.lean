/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor.PseudoCoherent.ModuleCat

/-!
# Lemma 15.103.3

@stack 0D2L
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory

universe u

/- Lemma 15.103.3 (0D2L): the source equality
`R lim (K ⊗ᴸ Mₙ) = K ⊗ᴸ R lim Mₙ` is represented by the homotopy-limit property of the
canonical total right derived inverse limit.  The reusable statement is presentation-independent
and uses the fixed-left view of the canonical two-variable derived tensor bifunctor. -/
@[stacks 0D2L "Lemma 15.103.3"]
#check @CategoryTheory.DerivedLimit.tensorSingleOfIsPseudoCoherent

/- The exact product-comparison input acts on the degree-zero family inside `D(A)`, so it plugs
directly into the Milnor-triangle preservation API. -/
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.piComparison_single_isIso
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.preservesLimit_single_of_piComparison_isIso
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.preservesLimit_single_of_isPseudoCoherent

/- Presentation-independent companion for a caller that already has some homotopy-limit object. -/
#check fun {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat A)) (hK : K.IsPseudoCoherent)
    (M : SequentialInverseSystem (ModuleCat A))
    {L : DerivedCategory (ModuleCat A)}
    (hL : HomotopyLimit.IsOf (M ⋙ ModuleCat.single0Functor) L) ↦
  hL.tensor_single_of_isPseudoCoherent hK

/- The concrete bridge identifying stagewise evaluation with degree-zero stage embedding is
independently reusable for other derived functors of inverse systems. -/
#check @CategoryTheory.DerivedLimit.Stage.singleTowerIso
#check @CategoryTheory.DerivedLimit.Stage.singleTowerIso_hom_app
#check @CategoryTheory.DerivedLimit.Stage.singleTowerIso_inv_app
