module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
import StacksCheckRecall

/-!
# Functoriality of derived tensor product under change of rings

This chapter file recalls the canonical right-variable functoriality API from `ReasLib`.

@stack 0BYK
-/

@[expose] public section

open CategoryTheory

universe u

variable {A : Type u} [CommRing A]
variable {L N : CochainComplex (ModuleCat A) ℤ} (f : L ⟶ N)

/- Lemma 15.60.2 (1), tag `0BYK`: a map of complexes of `A`-modules induces a natural
transformation between the corresponding fixed-right derived tensor functors over `A`. -/
@[stacks 0BYK "(1) induced derived tensor transformation"]
#check CategoryTheory.derivedTensorChangeOfRingsMapOfComplex (RingHom.id A) f

variable [QuasiIso f]

/- Lemma 15.60.2 (2), tag `0BYK`: if `f` is a quasi-isomorphism, the induced transformation
of fixed-right derived tensor functors over `A` is an isomorphism. -/
@[stacks 0BYK "(2) quasi-isomorphism induces a functor isomorphism"]
#check CategoryTheory.derivedTensorChangeOfRingsMapOfComplex_isIso (RingHom.id A) f

/- The reusable owner is stronger: it allows an arbitrary source ring map `R ⟶ A`. -/
#check @CategoryTheory.derivedTensorChangeOfRingsMapOfComplex
#check @CategoryTheory.derivedTensorChangeOfRingsMapOfComplex_isIso
#check @CategoryTheory.derivedTensorChangeOfRingsMap
#check @CategoryTheory.derivedTensorChangeOfRingsMap_app
#check @CategoryTheory.derivedTensorChangeOfRingsMap_isIso
