/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Ideal.Cotangent

@[expose] public section

open scoped AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The canonical map from an ideal to the sections of its cotangent module on an open
subset of the spectrum. -/
def cotangentToSections (I : Ideal A)
    (U : TopologicalSpace.Opens (PrimeSpectrum A)) :
    I →ₗ[A]
      (AlgebraicGeometry.modulesSpecToSheaf.obj
        (AlgebraicGeometry.tilde
          (ModuleCat.of (CommRingCat.of A) I.Cotangent))).presheaf.obj (.op U) :=
  (AlgebraicGeometry.tilde.toOpen
    (ModuleCat.of (CommRingCat.of A) I.Cotangent) U).hom.comp I.toCotangent

/-- The canonical map to cotangent sections sends an ideal element by first taking its
class in `I.Cotangent` and then restricting it to the given open. -/
theorem cotangentToSections_apply (I : Ideal A)
    (U : TopologicalSpace.Opens (PrimeSpectrum A)) (x : I) :
    I.cotangentToSections U x =
      (AlgebraicGeometry.tilde.toOpen
        (ModuleCat.of (CommRingCat.of A) I.Cotangent) U).hom (I.toCotangent x) := sorry

/-- The ideal obtained by mapping the kernel of the canonical cotangent-section map back
into the ambient ring. -/
def cotangentSectionsKernel (I : Ideal A)
    (U : TopologicalSpace.Opens (PrimeSpectrum A)) : Ideal A :=
  (LinearMap.ker (I.cotangentToSections U)).map I.subtype

/-- Membership in `I.cotangentSectionsKernel U` is the source kernel condition for
`I → Γ(U, I.Cotangent̃)`. -/
theorem mem_cotangentSectionsKernel (I : Ideal A)
    (U : TopologicalSpace.Opens (PrimeSpectrum A)) (x : A) :
    x ∈ I.cotangentSectionsKernel U ↔
      ∃ hx : x ∈ I, I.cotangentToSections U ⟨x, hx⟩ = 0 := sorry

/-- The cotangent-section kernel ideal is contained in the original ideal. -/
theorem cotangentSectionsKernel_le (I : Ideal A)
    (U : TopologicalSpace.Opens (PrimeSpectrum A)) :
    I.cotangentSectionsKernel U ≤ I := sorry

end Ideal
