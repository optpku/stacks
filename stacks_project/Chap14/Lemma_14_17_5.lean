module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.Natural
import StacksCheckRecall

/-!
@stack 017N
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasFiniteLimits C]
variable {U V W : SSet.{w}}
variable [U.ObjFinite] [V.ObjFinite] [W.ObjFinite]
variable [U.Nonempty] [V.Nonempty] [W.Nonempty]
variable (a : U ⟶ V) (b : U ⟶ W) (T : SimplicialObject C)
variable [U.EventuallyDegenerate]
variable [V.EventuallyDegenerate]
variable [W.EventuallyDegenerate]

/- Lemma 14.17.5 (017N) (1): Lemma 14.17.4 supplies the representation for maps out of `U`. -/
@[stacks 017N "Lemma 14.17.5 (1)"]
#check (presheaf.isRepresentable.ofEventuallyDegenerate U T :
  Functor.IsRepresentable (presheaf U T))

/- Lemma 14.17.5 (017N) (2): Lemma 14.17.4 supplies the representation for maps out of `V`. -/
@[stacks 017N "Lemma 14.17.5 (2)"]
#check (presheaf.isRepresentable.ofEventuallyDegenerate V T :
  Functor.IsRepresentable (presheaf V T))

/- Lemma 14.17.5 (017N) (3): Lemma 14.17.4 supplies the representation for maps out of `W`. -/
@[stacks 017N "Lemma 14.17.5 (3)"]
#check (presheaf.isRepresentable.ofEventuallyDegenerate W T :
  Functor.IsRepresentable (presheaf W T))

/- Lemma 14.17.5 (017N) (4): maps out of the pushout are representable; its dimension bound only
uses the two target legs. -/
@[stacks 017N "Lemma 14.17.5 (4)"]
#check (presheaf.isRepresentable.ofEventuallyDegenerate
    (CategoryTheory.Limits.pushout a b) T :
  Functor.IsRepresentable
    (presheaf (CategoryTheory.Limits.pushout a b) T))

variable {MU MV MW MP : SimplicialObject C}
variable (RU : (presheaf U T).RepresentableBy MU)
variable (RV : (presheaf V T).RepresentableBy MV)
variable (RW : (presheaf W T).RepresentableBy MW)
variable (RP :
  (presheaf (CategoryTheory.Limits.pushout a b) T).RepresentableBy MP)

/- Lemma 14.17.5 (017N) (5): under the finite nonempty and eventual-degeneracy hypotheses, the
object representing maps out of `pushout a b` is canonically isomorphic to the pullback of
arbitrary chosen representations for the three terms of the span. -/
@[stacks 017N "Lemma 14.17.5 (5)"]
#check (pushout.comparisonOf.isIso
  (a := a) (b := b) RU RV RW RP :
  IsIso (pushout.comparisonOf a b RU RV RW RP))

section CanonicalComparison

/- The finite/eventually-degenerate instance from ReasLib supplies all four internal-hom
objects, including the pushout, without chapter-local `letI` witnesses. -/
#check (inferInstance : HasInternalHoms U C)
#check (inferInstance : HasInternalHoms V C)
#check (inferInstance : HasInternalHoms W C)
#check (inferInstance :
  HasInternalHoms (CategoryTheory.Limits.pushout a b) C)

/- The reusable canonical form packages the comparison simultaneously for every target
simplicial object using the canonical finite representability instances. -/
#check (pushout.comparison.natIso (C := C) a b :
  internalHom.targetFunctor (C := C) (CategoryTheory.Limits.pushout a b) ≅
    pushout.pullback.functor (C := C) a b)

end CanonicalComparison

end CategoryTheory.SimplicialObject.internalHom
