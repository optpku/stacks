/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Presentation
public import ReasLib.RingTheory.RegularLocalRing.Parameters

/-!
# Associated Graded Rings of Regular Local Rings

This file owns the polynomial presentation of the associated graded ring of a
regular local ring.  The parameterized statement records the images of the
variables; the dimension-only statement is the canonical downstream entry
point.

@stack 00NO
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing

namespace IsLocalRing.IsRegularSystemOfParameters

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The canonical polynomial presentation attached to a regular system of
parameters is injective. Surjectivity follows formally from generation of the
maximal ideal. -/
@[stacks 00NO "regular-parameter associated-graded presentation injectivity"]
theorem associatedGradedMap_injective {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    Function.Injective
      (Ideal.AssociatedGraded.Presentation.map x) := sorry

/-- The canonical polynomial presentation attached to a regular system of
parameters is bijective. -/
@[stacks 00NO "regular-parameter associated-graded presentation"]
theorem associatedGradedMap_bijective {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    Function.Bijective
      (Ideal.AssociatedGraded.Presentation.map x) := by
  exact ⟨associatedGradedMap_injective hx,
    Ideal.AssociatedGraded.Presentation.map_surjective x hx.2.ge⟩

/-- The canonical associated-graded equivalence determined by a regular system
of parameters. Its inverse selects a polynomial only from the fully proved
surjectivity of the presentation. Injectivity is used solely for the
proposition-valued left inverse law. -/
@[stacks 00NO "regular-parameter associated-graded equivalence"]
noncomputable def associatedGradedEquiv {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    MvPolynomial (Fin d) (ResidueField R) ≃ₐ[ResidueField R]
      Ideal.AssociatedGraded.ring (maximalIdeal R) :=
  { Ideal.AssociatedGraded.Presentation.map x with
    invFun := Ideal.AssociatedGraded.Presentation.preimage x hx.2.ge
    left_inv := fun p ↦ associatedGradedMap_injective hx
      (Ideal.AssociatedGraded.Presentation.map_preimage x hx.2.ge
        (Ideal.AssociatedGraded.Presentation.map x p))
    right_inv := Ideal.AssociatedGraded.Presentation.map_preimage x hx.2.ge }

@[simp]
theorem associatedGradedEquiv_toAlgHom {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    (associatedGradedEquiv hx).toAlgHom =
      Ideal.AssociatedGraded.Presentation.map x :=
  rfl

/-- The reverse equivalence is the preimage selected from the proved
surjectivity of the canonical presentation. -/
theorem associatedGradedEquiv_symm_apply {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x)
    (y : Ideal.AssociatedGraded.ring (maximalIdeal R)) :
    (associatedGradedEquiv hx).symm y =
      Ideal.AssociatedGraded.Presentation.preimage x hx.2.ge y :=
  rfl

@[simp, stacks 00NO "regular-parameter associated-graded variable"]
theorem associatedGradedEquiv_X {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) (i : Fin d) :
    associatedGradedEquiv hx (MvPolynomial.X i) =
      Ideal.AssociatedGraded.degreeOne (x i) := by
  change Ideal.AssociatedGraded.Presentation.map x (MvPolynomial.X i) = _
  simp

/-- The inverse recovers the variable from the class of its regular parameter. -/
@[simp]
theorem associatedGradedEquiv_symm_degreeOne {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) (i : Fin d) :
    (associatedGradedEquiv hx).symm (Ideal.AssociatedGraded.degreeOne (x i)) =
      MvPolynomial.X i := by
  rw [← associatedGradedEquiv_X hx i]
  exact (associatedGradedEquiv hx).symm_apply_apply _

/-- A regular system of parameters presents the associated graded ring as a
polynomial algebra. The equation identifies the equivalence with the
canonical presentation map without selecting data outside this proposition. -/
@[stacks 00NO "regular-parameter associated-graded equivalence"]
theorem existsAssociatedGradedEquiv {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    ∃ e : MvPolynomial (Fin d) (ResidueField R) ≃ₐ[ResidueField R]
        Ideal.AssociatedGraded.ring (maximalIdeal R),
      e.toAlgHom = Ideal.AssociatedGraded.Presentation.map x := by
  exact ⟨associatedGradedEquiv hx, associatedGradedEquiv_toAlgHom hx⟩

end IsLocalRing.IsRegularSystemOfParameters

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The associated graded ring of a `d`-dimensional regular local ring is a
polynomial algebra in `d` variables over its residue field. -/
@[stacks 00NO "associated graded ring of a regular local ring"]
theorem associatedGradedEquivMvPolynomial {d : ℕ}
    (hdim : ringKrullDim R = d) :
    Nonempty
      (MvPolynomial (Fin d) (ResidueField R) ≃ₐ[ResidueField R]
        Ideal.AssociatedGraded.ring (maximalIdeal R)) := sorry

end IsRegularLocalRing
