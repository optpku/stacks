/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDDeRham

@[expose] public section
universe u
namespace CrystallinePDDeRham

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {J : Ideal B} {K : Ideal C} (δ : DividedPowers J) (ε : DividedPowers K)
variable (hDP : DividedPowers.IsDPMorphism δ ε (algebraMap B C))

/-- The canonical Kähler differential map, retaining the actual semilinear
scalar transport along the ring map. -/
noncomputable def kaehlerMap : Ω[B⁄A] →ₛₗ[algebraMap B C] Ω[C⁄A] where
  toFun := KaehlerDifferential.map A A B C
  map_add' := map_add (KaehlerDifferential.map A A B C)
  map_smul' b ω := by
    simpa only [algebraMap_smul] using (KaehlerDifferential.map A A B C).map_smul b ω

include hDP in
/-- A PD ring map carries the defining PD differential relations into the
target relations. The PD compatibility hypothesis is essential. -/
theorem kaehlerMap_relations :
    relations A B δ ≤ (relations A C ε).comap (kaehlerMap A B C) := sorry

/-- The actual map on PD one-forms, obtained by quotienting the canonical
Kähler map. No inverse to a differential quotient is introduced. -/
noncomputable def mapOneForms : oneForms A B δ →ₛₗ[algebraMap B C] oneForms A C ε :=
  (relations A B δ).mapQ (relations A C ε) (kaehlerMap A B C)
    (kaehlerMap_relations A B C δ ε hDP)

/-- The PD-form map sends db to d of the actual image of b. -/
theorem mapOneForms_derivation (b : B) :
    mapOneForms A B C δ ε hDP (derivation A B δ b) =
      derivation A C ε (algebraMap B C b) := by
  change (relations A C ε).mkQ (KaehlerDifferential.map A A B C
    (KaehlerDifferential.D A B b)) =
      (relations A C ε).mkQ (KaehlerDifferential.D A C (algebraMap B C b))
  rw [KaehlerDifferential.map_D]

end CrystallinePDDeRham
