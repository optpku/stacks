module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_10_Another_variant_for_Noetherian_BaseChange
public import stacks_project.Chap88.Definition_88_20_1_Ring

/-!
# Rig-étaleness is stable under completed base change by adic maps
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom
open Algebra.TensorProduct Algebra.TensorProduct.Completed

namespace TopologicalRing.Noetherian

/-- Lemma 88.19.4: On arrows of `WAdm^Noeth`, the morphism property
`P φ` = "`φ` is rig-étale" (`RingHom.RigEtale`) is stable under base
change by `Q φ` = "`φ` is adic" (`RingHom.IsAdicHom`), in the sense of
Formal Spaces, Remark 87.21.10: if `B → A` is rig-étale and `B → C` is
adic, then `Completed B A C` is adic Noetherian and `includeRight B A C`
is rig-étale. -/
@[stacks 0GCW]
theorem isStableUnderBaseChangeBy_rigEtale_isAdicHom :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom) :=
  sorry

end TopologicalRing.Noetherian

open TopologicalRing

namespace RingHom.RigEtale

/-- If `algebraMap B A` is a rig-étale homomorphism of Noetherian adic rings
and `algebraMap B C` is adic, then `includeRight B A C` is rig-étale once
`Completed B A C` is adic Noetherian. -/
theorem of_includeRight {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
    [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]
    [IsAdicRing (Completed B A C)] [IsNoetherianRing (Completed B A C)]
    [RigEtale (algebraMap B A)] (h : (algebraMap B C).IsAdicHom) :
    RigEtale (includeRight B A C) :=
  sorry

end RingHom.RigEtale
