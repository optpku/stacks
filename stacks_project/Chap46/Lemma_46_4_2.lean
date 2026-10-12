/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Injectives
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace ModuleValuedFunctor.Adequate

variable (A : CommRingCat.{u})

/- Lemma 46.4.2 (1): the inclusion of adequate module-valued functors into all
module-valued functors on `Alg_A` is fully faithful. -/
/- Lemma 46.4.2 -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.inclusion_fullyFaithful A :
    (ObjectProperty.ι (ModuleValuedFunctor.TensorAdequate (A := A))).FullyFaithful)

/- Lemma 46.4.2 (2): the inclusion of adequate module-valued functors into all
module-valued functors on `Alg_A` is exact. -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.inclusion_exact A :
    exactFunctor (ModuleValuedFunctor.TensorAdeq A)
      (ModuleValuedFunctor.bundled.{u, u} A)
      (ObjectProperty.ι (ModuleValuedFunctor.TensorAdequate (A := A))))

/- Lemma 46.4.2 (3): adequate module-valued functors form a weak Serre
subcategory of all module-valued functors on `Alg_A`. -/
@[stacks 06Z7] #check
  (@ModuleValuedFunctor.TensorAdequate.isWeakSerreClass A :
    ∀ h : Abelian (ModuleValuedFunctor.bundled.{u, u} A),
      @IsWeakSerreClass _ _ h (ModuleValuedFunctor.TensorAdequate (A := A)))

/- Lemma 46.4.2 (4): the category of module-valued functors on `Alg_A` has
enough injective objects. -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.ambientEnoughInjectives A :
    EnoughInjectives (ModuleValuedFunctor.bundled.{u, u} A))

/- Lemma 46.4.2 (5): the functor `Q` constructed in Lemma 46.4.1 is right
adjoint to the inclusion of adequate module-valued functors. -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.inclusion_adjunction A :
    ObjectProperty.ι (ModuleValuedFunctor.TensorAdequate (A := A)) ⊣
      @Functor.rightAdjoint _ _ _ _
        (ObjectProperty.ι (ModuleValuedFunctor.TensorAdequate (A := A)))
        (ModuleValuedFunctor.TensorAdequate.inclusion_isLeftAdjoint A))

/- Lemma 46.4.2 (6): the right adjoint `Q` to the inclusion of adequate
module-valued functors is left exact. -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.coreflector_leftExact A :
    leftExactFunctor (ModuleValuedFunctor.bundled.{u, u} A)
      (ModuleValuedFunctor.TensorAdeq A)
      (@Functor.rightAdjoint _ _ _ _
        (ObjectProperty.ι (ModuleValuedFunctor.TensorAdequate (A := A)))
        (ModuleValuedFunctor.TensorAdequate.inclusion_isLeftAdjoint A)))

/- Lemma 46.4.2 (7): the right adjoint `Q` to the inclusion of adequate
module-valued functors preserves injective objects. -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.coreflector_preservesInjectives A :
    (@Functor.rightAdjoint _ _ _ _
      (ObjectProperty.ι (ModuleValuedFunctor.TensorAdequate (A := A)))
      (ModuleValuedFunctor.TensorAdequate.inclusion_isLeftAdjoint A)).PreservesInjectiveObjects)

/- Lemma 46.4.2 (8): the category of adequate module-valued functors on
`Alg_A` has enough injective objects. -/
@[stacks 06Z7] #check
  (ModuleValuedFunctor.TensorAdequate.enoughInjectives A :
    EnoughInjectives (ModuleValuedFunctor.TensorAdeq A))

end ModuleValuedFunctor.Adequate
