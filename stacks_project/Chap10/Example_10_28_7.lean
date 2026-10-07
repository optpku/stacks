module

public import ReasLib.RingTheory.Ideal.Oka.ModuleQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-!
# The colon-ideal quotient sequence

@stack 0G1N

Example 10.28.7 is the ideal specialization of the reusable quotient sequence of a linear map.
The concrete colon sequence and its Oka-family consequence are owned by ReasLib.
-/

#check @LinearMap.QuotientSequence.shortComplex
#check @LinearMap.QuotientSequence.shortExact
#check @Ideal.colon_span_singleton_eq_comap_mulRight
#check @Ideal.range_mulRight_eq_span_singleton
#check @Ideal.Quotient.colonMul
#check @Ideal.Quotient.factorSupSpan
#check @Ideal.Quotient.colonMul_mk
#check @Ideal.Quotient.colonShortComplex

/- Example 10.28.7 (Tag 0G1N) (1): the standard colon-ideal quotient sequence is short exact. -/
@[stacks 0G1N "(1)"]
#check (@Ideal.Quotient.colonShortComplex_shortExact :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (a : A),
    (Ideal.Quotient.colonShortComplex I a).ShortExact)

/- Example 10.28.7 (Tag 0G1N) (2): extension-closed module properties define Oka families via
ideal quotients. -/
@[stacks 0G1N "(2)"]
#check (@Ideal.IsOka.ofQuotientModuleProperty :
  ∀ {A : Type u} [CommRing A] (P : ObjectProperty (ModuleCat.{u} A))
    [P.IsClosedUnderExtensions] [P.ContainsZero],
    Ideal.IsOka (fun I : Ideal A ↦ P (ModuleCat.of A (A ⧸ I))))
