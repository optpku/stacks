module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Cover
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (M : DifferentialGradedModule.{u, v} A)

/- Lemma 22.20.3 (09KN): every right DG module admits a bundled two-step property P cover which
is epic after forgetting the differential and epic on cycles. -/
@[stacks 09KN] #check
  (DifferentialGradedModule.PropertyP.Cover.nonempty A M :
    Nonempty (DifferentialGradedModule.PropertyP.Cover A M))
