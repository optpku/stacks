/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Properties
import StacksCheckRecall

/-!
# Remark 15.90.20

Formal-gluing equivalences detect finite generation, finite presentation,
flatness, and projectivity componentwise.  They also transport tensor
structures and hence induce equivalences on categories such as algebras.
The statements below record the commutative-ring specialization supported by
the current `ModuleCat` formal-gluing API.

@stack 05EU
-/

@[expose] public section

open CategoryTheory
open LocalizedModule.Away.FormalGluing
open scoped TensorProduct

universe u v

namespace Remark_15_90_20

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Flat R S]
variable (hquot :
  let I : Ideal R := Ideal.span (Set.range f)
  Function.Bijective
    (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
      (algebraMap R S) Ideal.le_comap_map))

/- Remark 15.90.20 (05EU): finite generation is detected by the base-change
component and all principal-localization components. -/
@[stacks 05EU "finite modules under formal gluing"]
#check (finite_iff_baseChange_and_localizedAway f hquot :
    Module.Finite R M ↔
      Module.Finite S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.Finite (Localization.Away (f i))
            (LocalizedModule.Away (f i) M))

/- Finite presentation is detected by the same components. -/
@[stacks 05EU "finitely presented modules under formal gluing"]
#check (finitePresentation_iff_baseChange_and_localizedAway f hquot :
    Module.FinitePresentation R M ↔
      Module.FinitePresentation S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.FinitePresentation (Localization.Away (f i))
            (LocalizedModule.Away (f i) M))

/- Flatness is detected by the same components. -/
@[stacks 05EU "flat modules under formal gluing"]
#check (flat_iff_baseChange_and_localizedAway f hquot :
    Module.Flat R M ↔
      Module.Flat S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.Flat (Localization.Away (f i))
            (LocalizedModule.Away (f i) M))

/- Projectivity is detected by the same components. -/
@[stacks 05EU "projective modules under formal gluing"]
#check (projective_iff_baseChange_and_localizedAway f hquot :
    Module.Projective R M ↔
      Module.Projective S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.Projective (Localization.Away (f i))
            (LocalizedModule.Away (f i) M))

/- The formal-gluing equivalences use the canonical module functor. -/
#check @LocalizedModule.Away.FormalGluing.ofModuleFunctor

/- Tensor structures transport across equivalences and induce equivalences
on monoid objects, including the algebra interpretation of module monoids. -/
@[stacks 05EU "tensor structures under formal gluing"]
#check @Monoidal.equivalenceTransported
#check @CategoryTheory.Equivalence.mapMon
#check @ModuleCat.monModuleEquivalenceAlgebra

end Remark_15_90_20
