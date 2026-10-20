module

public import ReasLib.RingTheory.Normal.Nagata
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.161.1

@stack 032F
-/

/- Definition 10.161.1 (1): An N-1 domain is a domain whose integral closure in its fraction
field is a finite module over the domain.

Definition 10.161.1 (2): An N-2 ring (Japanese domain) is a domain such that for every finite
extension of its fraction field, the integral closure is finite.

Owner: `IsN1Ring`, `IsN2Ring` in `ReasLib.RingTheory.Normal.Nagata`. -/
@[stacks 032F "(1)"]
#check @IsN1Ring
@[stacks 032F "(2)"]
#check @IsN2Ring
