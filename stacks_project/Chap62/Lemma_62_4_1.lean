module

public import stacks_project.Chap62.Lemma_62_4_1_Specialization

/-!
# Lemma 62.4.1

Specialization of associated cycles of a coherent module flat over a discrete
valuation ring.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (F : X.Modules) [F.IsCoherent] (r : ℕ)

/-- Lemma 62.4.1 (1): if `R` is a discrete valuation ring, `X` is locally of finite type
over `R`, and `F` is a coherent module on `X` flat over `R` whose support on the generic
fibre has dimension at most `r`, then the support of `F` on the special fibre has
dimension at most `r`. -/
@[stacks 0H4I]
theorem topologicalKrullDim_moduleSupport_specialFiber_le
    (hflat : flatOver F f)
    (hK : fiberSupportDimension f F
      (genericPoint (Spec (CommRingCat.of R))) ≤ (r : WithBot ℕ∞)) :
    fiberSupportDimension f F (IsLocalRing.closedPoint R) ≤ (r : WithBot ℕ∞) :=
  sorry

/-- Lemma 62.4.1 (2): under the same hypotheses, the specialization map
`cycleSpecialization` sends the degree-`r` associated cycle of `F` on the generic fibre
to the degree-`r` associated cycle of `F` on the special fibre. -/
@[stacks 0H4I]
theorem cycleSpecialization_associatedCycle
    (hflat : flatOver F f)
    (hK : fiberSupportDimension f F
      (genericPoint (Spec (CommRingCat.of R))) ≤ (r : WithBot ℕ∞)) :
    Hom.cycleSpecialization f r
        (fiberAssociatedCycle f F
          (genericPoint (Spec (CommRingCat.of R))) r) =
      fiberAssociatedCycle f F (IsLocalRing.closedPoint R) r :=
  sorry

end AlgebraicGeometry.Scheme.Modules

