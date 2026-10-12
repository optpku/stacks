/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Base change of algebra homomorphisms along localization

This leaf owns the algebra map obtained by localizing both sides of an
algebra homomorphism at a submonoid of the common base ring.
-/

universe u v w x

namespace AlgHom.Localization

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- The base change of an algebra homomorphism along localization at a
submonoid of its base ring. -/
@[stacks 07F4 "localization base change map"]
noncomputable abbrev baseChange (f : A →ₐ[R] B) (S : Submonoid R) :
    Localization (Algebra.algebraMapSubmonoid A S) →ₐ[Localization S]
      Localization (Algebra.algebraMapSubmonoid B S) :=
  IsLocalization.mapₐ S (Localization S)
    (Localization (Algebra.algebraMapSubmonoid A S))
    (Localization (Algebra.algebraMapSubmonoid B S)) f

/-- Localized base change sends the image of a source element to the image
of its value under the original algebra homomorphism. -/
@[simp]
theorem baseChange_algebraMap (f : A →ₐ[R] B) (S : Submonoid R) (a : A) :
    baseChange f S
        (algebraMap A (Localization (Algebra.algebraMapSubmonoid A S)) a) =
      algebraMap B (Localization (Algebra.algebraMapSubmonoid B S)) (f a) := sorry

/-- Localizing the identity algebra homomorphism gives the identity. -/
theorem baseChange_id (S : Submonoid R) :
    baseChange (AlgHom.id R A) S =
      AlgHom.id (Localization S)
        (Localization (Algebra.algebraMapSubmonoid A S)) := sorry

/-- Localized base change respects composition of algebra homomorphisms. -/
theorem baseChange_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (S : Submonoid R) :
    baseChange (g.comp f) S = (baseChange g S).comp (baseChange f S) := sorry

end AlgHom.Localization
