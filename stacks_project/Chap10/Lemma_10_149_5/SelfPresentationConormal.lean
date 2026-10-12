/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.SectionQuotient.Conormal
import StacksCheckRecall

/-!
Self-presentation conormal support for Lemma 10.149.5.

@stack 04EF
-/

@[expose] public section

@[stacks 04EF "cotangent-section generator"]
#check @Algebra.Extension.SectionQuotient.generator

@[stacks 04EF "cotangent-section generator evaluation"]
#check @Algebra.Extension.SectionQuotient.generator_apply

@[stacks 04EF "cotangent-section generator in the infinitesimal ring"]
#check @Algebra.Extension.SectionQuotient.generatorToInfinitesimal

@[stacks 04EF "cotangent-section generator evaluation in the infinitesimal ring"]
#check @Algebra.Extension.SectionQuotient.generatorToInfinitesimal_apply

@[stacks 04EF "cotangent-section image ideal"]
#check @Algebra.Extension.SectionQuotient.ideal

@[stacks 04EF "cotangent-section generator membership"]
#check @Algebra.Extension.SectionQuotient.generator_mem

@[stacks 04EF "cotangent-section ideal lies in the infinitesimal kernel"]
#check @Algebra.Extension.SectionQuotient.ideal_le_ker

@[stacks 04EF "quotient-linear conormal map"]
#check @KaehlerDifferential.Quotient.conormalToQuotient

@[stacks 04EF "quotient-linear conormal map on generators"]
#check @KaehlerDifferential.Quotient.conormalToQuotient_toCotangent

@[stacks 04EF "quotient-linear conormal exactness"]
#check @KaehlerDifferential.Quotient.conormalToQuotient_exact

@[stacks 04EF "cotangent-section generator differential in the conormal range"]
#check @Algebra.Extension.SectionQuotient.generator_differential_mem_range
