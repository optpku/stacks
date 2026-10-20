/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent comparison for kernels

An isomorphism between the domains of two ring maps to a common target transports the kernel
cotangent module.  The comparison morphism itself only uses the forward ring map; invertibility is
kept as a separate typeclass fact.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CommRingCat.Cotangent

variable {P Q T : CommRingCat.{u}}

/-- A commuting triangle of commutative-ring morphisms sends the first kernel ideal into the
pullback of the second kernel ideal. -/
theorem ker_le_comap (e : P ⟶ Q) (f : P ⟶ T) (g : Q ⟶ T)
    (triangle : e ≫ g = f) :
    RingHom.ker f.hom ≤ (RingHom.ker g.hom).comap e.hom := sorry

/-- The canonical forward comparison between the cotangent modules of two kernel ideals in a
commuting triangle of commutative-ring morphisms. -/
@[stacks 0D09 "kernel-cotangent comparison"]
noncomputable def kerComparison (e : P ⟶ Q) (f : P ⟶ T) (g : Q ⟶ T)
    (triangle : e ≫ g = f) :
    ModuleCat.of P (RingHom.ker f.hom).Cotangent ⟶
      (ModuleCat.restrictScalars e.hom).obj
        (ModuleCat.of Q (RingHom.ker g.hom).Cotangent) :=
  ConcreteCategory.ofHom (C := ModuleCat P)
    (@Ideal.mapCotangent
      P _ P Q _ _ (Algebra.id P) e.hom.toAlgebra
      (RingHom.ker f.hom) (RingHom.ker g.hom)
      (@Algebra.ofId P Q _ _ e.hom.toAlgebra)
      (ker_le_comap e f g triangle))

/-- The kernel-cotangent comparison sends a cotangent generator to the generator represented by
its image under the domain comparison. -/
@[stacks 0D09 "kernel-cotangent comparison on generators"]
theorem kerComparison_toCotangent (e : P ⟶ Q) (f : P ⟶ T) (g : Q ⟶ T)
    (triangle : e ≫ g = f) (z : RingHom.ker f.hom) :
    kerComparison e f g triangle ((RingHom.ker f.hom).toCotangent z) =
      (RingHom.ker g.hom).toCotangent
        ⟨e.hom z, ker_le_comap e f g triangle z.2⟩ := sorry

/-- If the domain comparison is an isomorphism, so is the induced comparison of kernel
cotangent modules. -/
@[stacks 0D09 "kernel-cotangent comparison is an isomorphism", instance]
instance kerComparison_isIso (e : P ⟶ Q) [IsIso e]
    (f : P ⟶ T) (g : Q ⟶ T) (triangle : e ≫ g = f) :
    IsIso (kerComparison e f g triangle) := sorry

end CommRingCat.Cotangent

-- The comparison data uses the forward ring morphism. Any `sorryAx` is confined to the
-- proof-valued ideal-membership field supplied by `ker_le_comap`.
