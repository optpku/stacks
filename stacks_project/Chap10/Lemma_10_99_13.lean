module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.CategoryTheory.Monoidal.Tor
import StacksCheckRecall

/-!
# Change of rings for first Tor of an extended ideal quotient

@stack 00MN
-/

@[expose] public section

open CategoryTheory ModuleCat

noncomputable section

universe u

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

namespace CategoryTheory.ModuleCat.Tor.QuotientBaseChange

/-- The extension `IS` of an ideal `I` along `R -> S`. -/
abbrev extendedIdeal (I : Ideal R) : Ideal S :=
  Ideal.map (algebraMap R S) I

/-- The quotient coefficient `S / IS`, regarded as an `S`-module. -/
abbrev quotientModule (I : Ideal R) : ModuleCat S :=
  ModuleCat.of S (S ⧸ extendedIdeal I)

/-- The scalar extension `S ⊗[R] M`. -/
abbrev baseChangedModule : ModuleCat S :=
  (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)

/-- The source `Tor_1^R(S / IS, M)`. -/
abbrev torOneQuotientSource (I : Ideal R) : ModuleCat R :=
  (((CategoryTheory.Tor (ModuleCat R) 1).obj
      (ModuleCat.of R (S ⧸ extendedIdeal I))).obj
    (ModuleCat.of R M))

/-- The target `Tor_1^S(S / IS, S ⊗[R] M)`. -/
abbrev torOneQuotientTarget (I : Ideal R) : ModuleCat S :=
  (((CategoryTheory.Tor (ModuleCat S) 1).obj (quotientModule I)).obj
    (@baseChangedModule R S M _ _ _ _ _))

/-- The target first Tor group after restriction of scalars to `R`. -/
abbrev torOneQuotientTargetRestrict (I : Ideal R) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((@torOneQuotientTarget R S M _ _ _ _ _ I) : ModuleCat S)

/-- The natural change-of-rings map
`Tor_1^R(S / IS, M) -> Tor_1^S(S / IS, S ⊗[R] M)`, with the target restricted to `R`. -/
@[stacks 00MN "natural comparison"]
noncomputable def comparison (I : Ideal R) :
    ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ⟶
      ((@torOneQuotientTargetRestrict R S M _ _ _ _ _ I) : ModuleCat R) := sorry

/-- **Lemma 10.99.13** ([Stacks tag 00MN](https://stacks.math.columbia.edu/tag/00MN)):
the natural change-of-rings map on first Tor is surjective. -/
@[stacks 00MN]
theorem comparison_surjective (I : Ideal R) :
    Function.Surjective (comparison (R := R) (S := S) (M := M) I) := sorry

end CategoryTheory.ModuleCat.Tor.QuotientBaseChange

@[stacks 00MN "Tor owner"]
#check @CategoryTheory.Tor

@[stacks 00MN "scalar extension"]
#check @ModuleCat.extendScalars

@[stacks 00MN "restriction of scalars"]
#check @ModuleCat.restrictScalars
