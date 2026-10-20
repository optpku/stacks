module

public import ReasLib.Algebra.Module.Projective.Schanuel
import StacksCheckRecall

@[expose] public section

/-!
# Schanuel's lemma

The reusable content is owned by the categorical projective-presentation API.  This file is the
source-facing compatibility entry point for Lemma 10.109.1.

@stack 00O3
-/

/- Lemma 10.109.1 at its lowest-parameter owner level: two projective presentations of one object
determine stably isomorphic kernels. -/
@[stacks 00O3 "projective-presentation owner"]
#check @CategoryTheory.ProjectivePresentation.schanuelIso

/- The short-exact-complex view retains the full stabilized comparison diagram and an arbitrary
identification of the quotient objects. -/
@[stacks 00O3 "short-exact-complex view"]
#check @CategoryTheory.ShortComplex.ShortExact.schanuelIso

@[stacks 00O3 "commutative Schanuel diagram"]
#check @CategoryTheory.ShortComplex.ShortExact.Schanuel.diagram

@[stacks 00O3 "right side of the Schanuel diagram"]
#check @CategoryTheory.ShortComplex.ShortExact.Schanuel.diagram_τ₃

/- Lemma 10.109.1 in the source's linear-map notation. -/
@[stacks 00O3 "linear-map view"]
#check @Module.Schanuel.ofExact

@[stacks 00O3 "existence of the source linear equivalence"]
#check @Module.Schanuel.nonempty_ofExact
