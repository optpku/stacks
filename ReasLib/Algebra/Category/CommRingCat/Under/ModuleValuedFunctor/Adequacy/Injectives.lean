/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Coreflection
public import ReasLib.CategoryTheory.Adjunction.Abelian
public import ReasLib.CategoryTheory.Adjunction.Exactness
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace ModuleValuedFunctor.TensorAdequate

variable (A : CommRingCat.{u})

/-! The categorical consequences of the tensor-adequate coreflection. -/

/-- The inclusion of tensor-adequate module-valued functors is fully faithful. -/
abbrev inclusion_fullyFaithful :
    (ObjectProperty.ι (TensorAdequate (A := A))).FullyFaithful :=
  ObjectProperty.fullyFaithfulι (TensorAdequate (A := A))

/-- Tensor-adequate objects form a weak Serre class in the ambient module-valued-functor category. -/
theorem isWeakSerreClass [Abelian (ModuleValuedFunctor.bundled.{u, u} A)] :
    IsWeakSerreClass (TensorAdequate (A := A)) := sorry

/-- The inclusion of tensor-adequate module-valued functors is exact. -/
theorem inclusion_exact :
    exactFunctor (TensorAdeq A) (ModuleValuedFunctor.bundled.{u, u} A)
      (ObjectProperty.ι (TensorAdequate (A := A))) := sorry

/-- The ambient category of module-valued functors has enough injective objects. -/
theorem ambientEnoughInjectives :
    EnoughInjectives (ModuleValuedFunctor.bundled.{u, u} A) := sorry

/-- The inclusion of tensor-adequate module-valued functors has its canonical left-adjoint structure. -/
theorem inclusion_isLeftAdjoint :
    (ObjectProperty.ι (TensorAdequate (A := A))).IsLeftAdjoint := sorry

/-- The inclusion of tensor-adequate module-valued functors has its canonical right adjoint. -/
noncomputable def inclusion_adjunction :
    ObjectProperty.ι (TensorAdequate (A := A)) ⊣
      @Functor.rightAdjoint _ _ _ _
        (ObjectProperty.ι (TensorAdequate (A := A))) (inclusion_isLeftAdjoint A) :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _
    (ObjectProperty.ι (TensorAdequate (A := A))) (inclusion_isLeftAdjoint A)

/-- The canonical right adjoint to the tensor-adequate inclusion is left exact. -/
theorem coreflector_leftExact :
    leftExactFunctor (ModuleValuedFunctor.bundled.{u, u} A) (TensorAdeq A)
      (@Functor.rightAdjoint _ _ _ _
        (ObjectProperty.ι (TensorAdequate (A := A))) (inclusion_isLeftAdjoint A)) := sorry

/-- The canonical right adjoint to the tensor-adequate inclusion preserves injective objects. -/
theorem coreflector_preservesInjectives :
    (@Functor.rightAdjoint _ _ _ _
      (ObjectProperty.ι (TensorAdequate (A := A))) (inclusion_isLeftAdjoint A)).PreservesInjectiveObjects := sorry

/-- The category of tensor-adequate module-valued functors has enough injective objects. -/
theorem enoughInjectives : EnoughInjectives (TensorAdeq A) := sorry

end ModuleValuedFunctor.TensorAdequate
