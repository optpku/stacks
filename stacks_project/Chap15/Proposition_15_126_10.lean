module

public import ReasLib.RingTheory.Normal.PrincipalQuotient.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 15.126.10

@stack 0BWZ

The catenary reduced-principal-quotient theorem is owned by ReasLib.
-/

/- Proposition 15.126.10: choose a reduced principal section inside a nonzero radical ideal. -/
@[stacks 0BWZ "Proposition 15.126.10, reduced principal quotient inside a radical ideal"]
#check @IsNormalRing.ReducedPrincipalQuotient.exists_mem_radical
