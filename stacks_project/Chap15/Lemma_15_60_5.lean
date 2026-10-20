module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.Composition
import StacksCheckRecall

/-!
Lemma 15.60.5 (08YU): for a tower `A ⟶ B ⟶ C`, the iterated derived tensor functor is identified
with direct change of rings along the composite.  The reusable owner is
`CategoryTheory.DerivedCategory.DerivedTensor.ChangeOfRings.compIso`; its explicit fixed-right
model parameter
records the model boundary instead of rebuilding a local monoidal instance.  The source-facing
aligned commutative-ring specialization uses `compIsoApp` for `M : D(A)`, `N : D(B)`, and
`K : D(C)`.  The companions `baseChangeIso` and `interchangeIso` encode the source's
base-change form and signed canonical comparison.  Since these APIs are stated for arbitrary
derived objects, the source's final complex-level clause is obtained by specializing objects to
`DerivedCategory.Q.obj` of cochain complexes.

@stack 08YU
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.DerivedTensor.ChangeOfRings

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [MonoidalCategory (DerivedCategory (ModuleCat C))]

variable (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat C))
variable (σ : A →+* B) (τ : B →+* C)
variable (N : DerivedCategory (ModuleCat B)) (K : DerivedCategory (ModuleCat C))
  (M : DerivedCategory (ModuleCat A))

/- Lemma 15.60.5 (08YU), functor-level comparison. -/
@[stacks 08YU "three-ring derived tensor functor comparison"]
#check compIso T σ τ N K

/- Lemma 15.60.5 (08YU), object-level comparison for `M`. -/
@[stacks 08YU "three-ring derived tensor object comparison"]
#check compIsoApp T σ τ N K M

/- The transported middle factor used by the direct functor. -/
@[stacks 08YU "transported middle derived tensor factor"]
#check rightFactor τ N K

/- Lemma 15.60.5 (08YU), base-change form of the object comparison. -/
@[stacks 08YU "base-change form of the object comparison"]
#check baseChangeIso T σ τ N K M

/- Lemma 15.60.5 (08YU), signed interchange comparison. -/
@[stacks 08YU "signed derived tensor interchange"]
#check interchangeIso T σ τ N K M

section Complexes

variable (M₀ : CochainComplex (ModuleCat A) ℤ)
variable (N₀ : CochainComplex (ModuleCat B) ℤ)
variable (K₀ : CochainComplex (ModuleCat C) ℤ)

/- The complex-level clause is the direct `Q.obj` specialization of the objectwise owner. -/
@[stacks 08YU "complex-level specialization of derived tensor composition"]
#check
  compIsoApp T σ τ (DerivedCategory.Q.obj N₀) (DerivedCategory.Q.obj K₀)
    (DerivedCategory.Q.obj M₀)

end Complexes

end CategoryTheory.DerivedCategory.DerivedTensor.ChangeOfRings
