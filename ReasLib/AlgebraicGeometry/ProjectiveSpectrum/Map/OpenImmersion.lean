module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist

/-!
# Open-immersion criteria for maps of projective spectra
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]

/-- A degree-zero element whose homogeneous localization map is an isomorphism makes the
natural domain of the induced `Proj` map equal to the whole target. -/
theorem projMapDomain_eq_top_of_isIso_awayMap
    (psi : calA →+*ᵍ calB) (g : calA 0)
    (hpsig : IsUnit (psi g))
    [IsIso (CommRingCat.ofHom
      (Localization.awayLift psi.toRingHom (g : A) hpsig))] :
    projMapDomain psi = ⊤ := by
  classical
  apply le_antisymm le_top
  rw [projMapDomain, Proj.iSup_basicOpen_eq_top]
  intro x hx
  rw [show (HomogeneousIdeal.irrelevant calB).toIdeal =
      RingHom.ker (GradedRing.projZeroRingHom calB) from rfl] at hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Localization.awayLift psi.toRingHom (g : A) hpsig))).2 x
  obtain ⟨a, v, hav⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (g : A)) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp v.property
  let vpow : Submonoid.powers (g : A) := ⟨(g : A) ^ n, by
    exact ⟨n, rfl⟩⟩
  have hv : vpow = v :=
    Subtype.ext hn
  rw [← hv] at hav
  rw [← Localization.mk_eq_mk'_apply] at hav
  have hxa : x * (psi g) ^ n = psi a := by
    rw [← hz]
    rw [← hav]
    dsimp [vpow]
    change (Localization.awayLift psi.toRingHom (g : A) hpsig
      (Localization.mk a ⟨(g : A)^n, ⟨n, rfl⟩⟩)) * (psi g)^n = psi a
    obtain ⟨v0, hv0⟩ := (isUnit_iff_exists_inv.mp hpsig)
    rw [Localization.awayLift_mk psi.toRingHom (g : A) a v0 hv0 n]
    calc
      psi a * v0 ^ n * (psi g) ^ n = psi a * (psi g * v0) ^ n := by
        rw [mul_pow]
        ac_rfl
      _ = psi a := by rw [hv0, one_pow, mul_one]
  have hpsi_a_irrel : psi a ∈ (HomogeneousIdeal.irrelevant calB).toIdeal := by
    rw [show (HomogeneousIdeal.irrelevant calB).toIdeal =
      RingHom.ker (GradedRing.projZeroRingHom calB) from rfl, RingHom.mem_ker]
    rw [← hxa, map_mul]
    simp [hx]
  let I : Ideal B := Ideal.span (Set.range fun f : PositiveHomogeneous calA => psi f.val)
  have hpsi_a_memI : psi a ∈ I := by
    rw [← DirectSum.sum_support_decompose calB (psi a)]
    apply Ideal.sum_mem
    intro d hd
    by_cases hd0 : d = 0
    · subst d
      have hz0 : DirectSum.decompose calB (psi a) 0 = 0 := Subtype.ext hpsi_a_irrel
      rw [hz0]
      exact I.zero_mem
    · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
      apply Ideal.subset_span
      refine ⟨⟨(DirectSum.decompose calA a d : A), d, hpos,
        (DirectSum.decompose calA a d).property⟩, ?_⟩
      exact map_directSumDecompose (𝒜 := calA) (ℬ := calB) psi
  have hxu : x * (psi g) ^ n ∈ I := by simpa [hxa] using hpsi_a_memI
  have hxI : x ∈ I := by
    have hu := (hpsig.pow n).mul_val_inv
    have heq : x = (↑((hpsig.pow n).unit⁻¹) : B) * (x * (psi g) ^ n) := by
      have hu' : (↑((hpsig.pow n).unit⁻¹) : B) * (psi g) ^ n = 1 := by
        simpa [mul_comm] using hu
      calc
        x = 1 * x := by rw [one_mul]
        _ = ((↑((hpsig.pow n).unit⁻¹) : B) * (psi g) ^ n) * x := by rw [hu']
        _ = (↑((hpsig.pow n).unit⁻¹) : B) * (x * (psi g) ^ n) := by ac_rfl
    rw [heq]
    exact I.mul_mem_left _ hxu
  change x ∈ I at hxI
  exact hxI

/-- Under the localization-isomorphism hypothesis, the canonical projective-spectrum map
associated to a graded map is an open immersion. -/
theorem projMapMap_isOpenImmersion_of_isIso_awayMap
    (psi : calA →+*ᵍ calB) (g : calA 0)
    (hpsig : IsUnit (psi g))
    [IsIso (CommRingCat.ofHom
      (Localization.awayLift psi.toRingHom (g : A) hpsig))] :
    IsOpenImmersion (projMapMap psi) := sorry

/-- The range of the canonical projective-spectrum map is the inverse image of the degree-zero
basic open when the homogeneous localization map is an isomorphism. -/
theorem projMapMap_range_eq_preimage_basicOpen_toSpecZero_of_isIso_awayMap
    (psi : calA →+*ᵍ calB) (g : calA 0)
    (hpsig : IsUnit (psi g))
    [IsIso (CommRingCat.ofHom
      (Localization.awayLift psi.toRingHom (g : A) hpsig))] :
    Set.range (projMapMap psi) =
      ((Proj.toSpecZero calA) ⁻¹ᵁ PrimeSpectrum.basicOpen g : Set (Proj calA)) := sorry

/-- The degreewise twist comparison of an induced projective-spectrum map is an isomorphism
when the homogeneous localization map is an isomorphism. -/
theorem projMapTheta_isIso_of_isIso_awayMap
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (psi : calA →+*ᵍ calB) (g : calA 0)
    (hpsig : IsUnit (psi g))
    [IsIso (CommRingCat.ofHom
      (Localization.awayLift psi.toRingHom (g : A) hpsig))] (n : Int) :
    IsIso (projMapTheta PcalA PcalB psi n) := sorry

end

end AlgebraicGeometry
