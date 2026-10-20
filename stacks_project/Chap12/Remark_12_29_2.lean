module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Counterexample
import StacksCheckRecall

/-!
# Remark 12.29.2

The reusable change-of-rings criteria and the residue-field counterexample are owned by `ReasLib`.
-/

@[expose] public section

open CategoryTheory
open ModuleCat

universe u

section Criteria

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S)

/- Remark 12.29.2 (1) [03B8]: restriction of scalars is exact. -/
@[stacks 03B8]
#check (ModuleCat.restrictScalars_exact f :
  exactFunctor (ModuleCat.{u} S) (ModuleCat.{u} R) (restrictScalars.{u} f))

/- Remark 12.29.2 (2) [03B8]: tensor extension and restriction of scalars form the canonical
adjunction. -/
#check (extendRestrictScalarsAdj.{u} f :
  extendScalars.{u, u, u} f ⊣ restrictScalars.{u} f)

/- Remark 12.29.2 (3) [03B8]: extension of scalars is right exact. -/
#check (ModuleCat.extendScalars_rightExact f :
  rightExactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
    (extendScalars.{u, u, u} f))

/- Flatness is the exactness criterion for the tensor left adjoint. -/
#check (ModuleCat.extendScalars_exact_iff_flat f :
  exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (extendScalars.{u, u, u} f) ↔
    f.Flat)

/- Remark 12.29.2 (4) [03B8]: restriction of scalars preserves all injective objects exactly
when the ring map is flat. -/
#check (ModuleCat.RestrictScalars.preservesInjectiveObjects_iff_flat f :
  (restrictScalars.{u} f).PreservesInjectiveObjects ↔ f.Flat)

end Criteria

/- Remark 12.29.2 (5) [03B8]: the generic non-flatness criterion and its residue-field
specialization are owned by the change-of-rings support API. -/
@[stacks 03B8]
#check @ModuleCat.RestrictScalars.not_preservesInjectiveObjects_of_not_flat

@[stacks 03B8]
#check @ModuleCat.RestrictScalars.intToZMod_not_preservesInjectiveObjects
