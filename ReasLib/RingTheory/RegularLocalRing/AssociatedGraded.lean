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
  refine ⟨associatedGradedMap_injective hx,
    Ideal.AssociatedGraded.Presentation.map_surjective x ?_⟩
  calc
    maximalIdeal R = parameterIdeal x := hx.2.symm
    _ = Ideal.span (Set.range fun i ↦ (x i : R)) := parameterIdeal_eq_span x
    _ ≤ Ideal.span (Set.range fun i ↦ (x i : R)) := le_rfl

/-- The canonical associated-graded equivalence determined by a regular system
of parameters. -/
@[stacks 00NO "regular-parameter associated-graded equivalence"]
noncomputable def associatedGradedEquiv {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    MvPolynomial (Fin d) (ResidueField R) ≃ₐ[ResidueField R]
      Ideal.AssociatedGraded.ring (maximalIdeal R) :=
  AlgEquiv.ofBijective _ (associatedGradedMap_bijective hx)

@[simp]
theorem associatedGradedEquiv_toAlgHom {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    (associatedGradedEquiv hx).toAlgHom =
      Ideal.AssociatedGraded.Presentation.map x :=
  rfl

@[simp, stacks 00NO "regular-parameter associated-graded variable"]
theorem associatedGradedEquiv_X {d : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) (i : Fin d) :
    associatedGradedEquiv hx (MvPolynomial.X i) =
      Ideal.AssociatedGraded.degreeOne (x i) := by
  change Ideal.AssociatedGraded.Presentation.map x (MvPolynomial.X i) = _
  simp

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
