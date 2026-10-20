module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.FiberwiseEquivalence
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Slice.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# A universe-polymorphic fiber-class criterion for stacks in groupoids

The source condition is expressed at the `CartesianBasedFunctor` layer. A cartesian functor from a
groupoid fibration to a stack in groupoids reflects the stack condition when it is faithful on
every fiber and the associated fiber-pair isomorphism-class presheaves are sheaves.
-/

@[expose] public section

universe uC vC uS vS uT vT

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} {T : Type uT}
variable [Category.{vS} S] [Category.{vT} T]
variable {pS : S ⥤ C} {pT : T ⥤ C}

namespace CartesianBasedFunctor

variable [pS.IsFibered]

/-- Every cartesian slice base change of `F` has a sheaf of fiberwise isomorphism classes. -/
@[stacks 0CKJ "universe-polymorphic slice fiber-class sheaf condition"]
def sliceFiberClasses.isSheaf
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor pS pT) : Prop :=
  sliceFiberClasses.satisfies
    (fun U ↦
      (Presheaf.IsSheaf (J.over U) :
        ObjectProperty
          ((Over U)ᵒᵖ ⥤ Type (max uC vC uS vT)))) F

/-- The source-facing sheaf condition: the selected fiber-pair presheaf associated to every
object of every target fiber is a sheaf on the corresponding slice site. -/
@[stacks 0CKJ "universe-polymorphic fiber-object slice sheaf condition"]
def fiberPairClasses.isSheaf
    [pT.IsFibered]
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor pS pT) : Prop :=
  fiberPairClasses.satisfies
    (fun U ↦
      (Presheaf.IsSheaf (J.over U) :
        ObjectProperty
          ((Over U)ᵒᵖ ⥤ Type (max uC vC uS vT)))) F

/-- The all-slice predicate unfolds to the sheaf condition for every cartesian slice base change. -/
@[stacks 0CKJ "universe-polymorphic slice criterion expansion"]
theorem sliceFiberClasses.isSheaf_iff
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor pS pT) :
    sliceFiberClasses.isSheaf J F ↔
      ∀ {U : C} (G : CartesianBasedFunctor.Yoneda.hom pT U),
        Presheaf.IsSheaf (J.over U) (sliceFiberClasses F G) := sorry

/-- The fiber-pair predicate unfolds to the sheaf condition for every selected target-fiber pair. -/
@[stacks 0CKJ "universe-polymorphic fiber-pair criterion expansion"]
theorem fiberPairClasses.isSheaf_iff
    [pT.IsFibered]
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor pS pT) :
    fiberPairClasses.isSheaf J F ↔
      ∀ {U : C} (y : pT.Fiber U),
        Presheaf.IsSheaf (J.over U) (fiberPairClasses F y) := sorry

/-- Fibered Yoneda identifies the source-facing fiber-object sheaf condition with the condition
for every cartesian slice morphism. -/
@[stacks 0CKJ "universe-polymorphic fiber-pair and slice criterion equivalence"]
theorem fiberPairClasses.isSheaf_iff_slice
    [pT.IsFibered]
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor pS pT) :
    fiberPairClasses.isSheaf J F ↔
      sliceFiberClasses.isSheaf J F := sorry

end CartesianBasedFunctor

namespace IsStack.InGroupoids

variable [Functor.IsFibered.InGroupoids pS]

/-- Lemma 8.6.11 (Stacks 0CKJ): a cartesian functor that is faithful on every fiber and whose
fiber-pair isomorphism-class presheaves are sheaves reflects the stack-in-groupoids property from
its target to its source. -/
@[stacks 0CKJ]
theorem ofCartesianFiberFaithful
    {J : GrothendieckTopology C}
    (F : CartesianBasedFunctor pS pT) [IsStack.InGroupoids J pT]
    (hFaithful : ∀ U : C, (F.fiberFunctor U).Faithful)
    (hSheaf : CartesianBasedFunctor.fiberPairClasses.isSheaf J F) :
    IsStack.InGroupoids J pS := sorry

/-- Total faithfulness gives the same universe-polymorphic stack criterion; the fiberwise
hypothesis is recovered by the cartesian fiberwise faithfulness criterion. -/
@[stacks 0CKJ "total-faithful universe-polymorphic stack criterion"]
theorem ofCartesianFaithful
    {J : GrothendieckTopology C}
    (F : CartesianBasedFunctor pS pT) [IsStack.InGroupoids J pT]
    (hFaithful : (F.toFunctor).Faithful)
    (hSheaf : CartesianBasedFunctor.fiberPairClasses.isSheaf J F) :
    IsStack.InGroupoids J pS := sorry

/-- The representation-independent all-slice sheaf condition gives the same
universe-polymorphic stack-in-groupoids criterion. -/
@[stacks 0CKJ "slice-form universe-polymorphic stack criterion"]
theorem ofCartesianFiberFaithful.slices
    {J : GrothendieckTopology C}
    (F : CartesianBasedFunctor pS pT) [IsStack.InGroupoids J pT]
    (hFaithful : ∀ U : C, (F.fiberFunctor U).Faithful)
    (hSheaf : CartesianBasedFunctor.sliceFiberClasses.isSheaf J F) :
    IsStack.InGroupoids J pS := sorry

/-- Total faithfulness and the representation-independent all-slice sheaf condition reflect the
stack-in-groupoids property from the target. -/
@[stacks 0CKJ "slice-form total-faithful stack criterion"]
theorem ofCartesianFaithful.slices
    {J : GrothendieckTopology C}
    (F : CartesianBasedFunctor pS pT) [IsStack.InGroupoids J pT]
    (hFaithful : (F.toFunctor).Faithful)
    (hSheaf : CartesianBasedFunctor.sliceFiberClasses.isSheaf J F) :
    IsStack.InGroupoids J pS := sorry

end IsStack.InGroupoids

end CategoryTheory
