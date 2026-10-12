/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Definition 12.20.1 (tag `011N`): an ungraded spectral sequence is the one-object-page
specialization of mathlib's spectral-sequence owner. Its morphisms and page-to-page homology
identifications are already the canonical category-theoretic API. -/
@[stacks 011N]
#check (SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1)

#check (@SpectralSequence.Hom C _ _ PUnit.{1}
  (fun _ ↦ ComplexShape.refl PUnit.{1}) 1)
#check (inferInstance : Category (SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1))
#check (SpectralSequence.pageFunctor C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1 (1 : ℤ))
#check (SpectralSequence.pageHomologyNatIso C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1
  (1 : ℤ) (2 : ℤ) PUnit.unit)

end CategoryTheory
