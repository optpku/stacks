module

public import ReasLib.RingTheory.Algebra.TensorProduct.FaithfullyFlat
import StacksCheckRecall

/-!
# Faithfully flat algebras from universally injective maps with flat coprojections

If the coprojections of an algebra into its tensor square are flat and the
structure map is universally injective, then the algebra is faithfully flat.
-/

@[expose] public section

open scoped TensorProduct

universe u v

/- Lemma 106.16.4. Let `B → C` be a ring map. If the coprojections
`C → C ⊗[B] C` are flat and `B → C` is universally injective, then `B → C`
is faithfully flat. -/
@[stacks 0GRM] #check
  (Module.FaithfullyFlat.of_universallyInjective_of_coprojections_flat :
    ∀ {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra B C],
      (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] C).Flat →
      (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom.Flat →
      LinearMap.UniversallyInjective.{u, u, v, max u v} (Algebra.linearMap B C) →
      Module.FaithfullyFlat B C)
