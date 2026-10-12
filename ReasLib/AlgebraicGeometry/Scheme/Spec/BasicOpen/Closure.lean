/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Affine

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Spec.BasicOpenUnion

noncomputable section

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The union of the principal open subsets associated to a finite family of ring elements. -/
abbrev union (f : Fin n → A) : (Spec (CommRingCat.of A)).Opens :=
  ⨆ i : Fin n, (Spec (CommRingCat.of A)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f i))

/-- The ring homomorphism to the product of the localizations away from a finite family. -/
def localizationProductMap (f : Fin n → A) :
    A →+* (∀ i : Fin n, Localization.Away (f i)) :=
  RingHom.pi (fun i : Fin n ↦ algebraMap A (Localization.Away (f i)))

/-- The kernel of the homomorphism to the product of the principal localizations. -/
abbrev closureIdeal (f : Fin n → A) : Ideal A :=
  RingHom.ker (localizationProductMap f)

/-- The defining ideal sheaf of the closure of a finite union of principal opens is the
kernel ideal sheaf of the spectrum map induced by the product of the principal localizations. -/
theorem schemeTheoreticClosureIdeal_eq_ker_specMap_localizationProductMap
    (f : Fin n → A) :
    schemeTheoreticClosureIdeal (union f) =
      (Spec.map (CommRingCat.ofHom (localizationProductMap f))).ker := by
  let cover := Scheme.Opens.iSupOpenCover
    (X := Spec (CommRingCat.of A))
    (fun i : Fin n ↦ (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f i)))
  have hU : IsRetrocompact
      (union f : Set (Spec (CommRingCat.of A))) := by
    rw [union, TopologicalSpace.Opens.coe_iSup]
    exact IsRetrocompact.iUnion fun i ↦
      isRetrocompact_basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f i))
  have hqc : QuasiCompact (union f).ι :=
    quasiCompact_iff_isSpectralMap.mpr
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hU)
  have hcover :
    (⨅ i : Fin n,
        (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
          ((Spec (CommRingCat.of A)).basicOpen
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f i)))).ker) =
      (union f).ι.ker := by
    simpa only [cover, Scheme.Opens.iSupOpenCover, union,
      Scheme.homOfLE_ι] using
      (@Scheme.Hom.iInf_ker_openCover_map_comp _ _ (union f).ι hqc cover)
  have hcomponent (i : Fin n) :
      (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
        ((Spec (CommRingCat.of A)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f i)))).ker =
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away (f i))))).ker := by
    have hopen := basicOpen_eq_of_affine (R := CommRingCat.of A) (f i)
    have hmap := basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) (f i)
    have hker := Scheme.Hom.ker_comp_of_isIso
      (basicOpenIsoSpecAway (R := CommRingCat.of A) (f i)).hom
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (f i)))))
    rw [hmap] at hker
    rw [hopen]
    exact hker
  have hpi :
      RingHom.ker (localizationProductMap f) =
        ⨅ i : Fin n, RingHom.ker (algebraMap A (Localization.Away (f i))) := by
    ext x
    simp [localizationProductMap, RingHom.mem_ker, funext_iff]
  have hspec :
      (⨅ i : Fin n,
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away (f i))))).ker) =
        (Spec.map (CommRingCat.ofHom (localizationProductMap f))).ker := by
    simp_rw [Scheme.Hom.ker_specMap]
    let E := Scheme.IdealSheafData.equivOfIsAffine
      (X := Spec (CommRingCat.of A))
    change
      (⨅ i : Fin n, E.symm
        ((RingHom.ker (algebraMap A (Localization.Away (f i)))).map
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) =
      E.symm ((RingHom.ker (localizationProductMap f)).map
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    let K : Fin n → Ideal Γ(Spec (CommRingCat.of A), ⊤) := fun i ↦
      (RingHom.ker (algebraMap A (Localization.Away (f i)))).map
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    have hK : (⨅ i : Fin n, K i) =
        (RingHom.ker (localizationProductMap f)).map
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
      rw [hpi]
      let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
      change (⨅ i : Fin n, (RingHom.ker
        (algebraMap A (Localization.Away (f i)))).map e) =
          (⨅ i : Fin n, RingHom.ker
            (algebraMap A (Localization.Away (f i)))).map e
      calc
        (⨅ i : Fin n, (RingHom.ker
            (algebraMap A (Localization.Away (f i)))).map e) =
            ⨅ i : Fin n, (RingHom.ker
              (algebraMap A (Localization.Away (f i)))).comap e.symm := by
          exact congrArg
            (fun g : Fin n → Ideal Γ(Spec (CommRingCat.of A), ⊤) ↦ ⨅ i, g i)
            (funext fun i ↦ Ideal.map_comap_of_equiv e)
        _ = (⨅ i : Fin n, RingHom.ker
            (algebraMap A (Localization.Away (f i)))).comap e.symm :=
          (Ideal.comap_iInf
            (e.symm : Γ(Spec (CommRingCat.of A), ⊤) →+* A)
            (fun i : Fin n ↦
              RingHom.ker (algebraMap A (Localization.Away (f i))))).symm
        _ = (⨅ i : Fin n, RingHom.ker
            (algebraMap A (Localization.Away (f i)))).map e :=
          (Ideal.map_comap_of_equiv e).symm
    exact (E.symm.toOrderIso.map_iInf K).symm.trans (congrArg E.symm hK)
  change (union f).ι.ker = _
  rw [← hcover]
  simp_rw [hcomponent]
  exact hspec

/-- The scheme-theoretic closure of a finite union of principal opens is canonically
isomorphic to the spectrum of the quotient by the localization-product kernel. -/
noncomputable def schemeTheoreticClosureIso (f : Fin n → A) :
    schemeTheoreticClosure (union f) ≅
      Spec (CommRingCat.of (A ⧸ closureIdeal f)) :=
  let q : Spec (CommRingCat.of (A ⧸ closureIdeal f)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (closureIdeal f)))
  let i := schemeTheoreticClosureι (union f)
  let hqClosed : IsClosedImmersion q := by
    dsimp only [q]
    exact IsClosedImmersion.spec_of_quotient_mk
      (R := CommRingCat.of A) (closureIdeal f)
  let hiPre : IsPreimmersion i := by
    dsimp only [i, schemeTheoreticClosureι]
    exact Scheme.IdealSheafData.instIsPreimmersionSubschemeι
      (schemeTheoreticClosureIdeal (union f))
  let hiClosed : IsClosedImmersion i := by
    dsimp only [i, schemeTheoreticClosureι]
    exact @IsClosedImmersion.of_isPreimmersion _ _
      (schemeTheoreticClosureIdeal (union f)).subschemeι
      (Scheme.IdealSheafData.instIsPreimmersionSubschemeι
        (schemeTheoreticClosureIdeal (union f)))
      ((schemeTheoreticClosureIdeal (union f)).range_subschemeι ▸
        (schemeTheoreticClosureIdeal (union f)).support.isClosed)
  let hqMono : Mono q :=
    @SurjectiveOnStalks.mono_of_injective _ _ q hqClosed.toSurjectiveOnStalks
      hqClosed.isClosedEmbedding.injective
  let hiMono : Mono i :=
    @SurjectiveOnStalks.mono_of_injective _ _ i hiPre.toSurjectiveOnStalks
      hiPre.isEmbedding.injective
  let h : q.ker = i.ker := by
    have hq : q.ker = schemeTheoreticClosureIdeal (union f) := by
      calc
        q.ker = (Spec.map (CommRingCat.ofHom (localizationProductMap f))).ker := by
          rw [Scheme.Hom.ker_specMap, Scheme.Hom.ker_specMap]
          change Scheme.IdealSheafData.ofIdealTop
              ((RingHom.ker (Ideal.Quotient.mk (closureIdeal f))).map
                (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
            Scheme.IdealSheafData.ofIdealTop
              ((closureIdeal f).map
                (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
          rw [Ideal.mk_ker]
        _ = schemeTheoreticClosureIdeal (union f) :=
          (schemeTheoreticClosureIdeal_eq_ker_specMap_localizationProductMap f).symm
    have hiKer : i.ker = schemeTheoreticClosureIdeal (union f) := by
      dsimp only [i, schemeTheoreticClosureι]
      with_unfolding_all
        exact Scheme.IdealSheafData.ker_subschemeι
          (schemeTheoreticClosureIdeal (union f))
    exact hq.trans hiKer.symm
  let hom := @IsClosedImmersion.lift _ _ _ q i hqClosed h.le
  let inv := @IsClosedImmersion.lift _ _ _ i q hiClosed h.ge
  have hom_fac : hom ≫ q = i :=
    @IsClosedImmersion.lift_fac _ _ _ q i hqClosed h.le
  have inv_fac : inv ≫ i = q :=
    @IsClosedImmersion.lift_fac _ _ _ i q hiClosed h.ge
  { hom := hom
    inv := inv
    hom_inv_id := hiMono.right_cancellation _ _ (by
      rw [Category.assoc, inv_fac, hom_fac, Category.id_comp])
    inv_hom_id := hqMono.right_cancellation _ _ (by
      rw [Category.assoc, hom_fac, inv_fac, Category.id_comp]) }

/-- The closure isomorphism commutes with the closed immersions into the affine spectrum. -/
theorem schemeTheoreticClosureIso_hom_comp_quotientMap (f : Fin n → A) :
    (schemeTheoreticClosureIso f).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (closureIdeal f))) =
        schemeTheoreticClosureι (union f) := by
  simp [schemeTheoreticClosureIso]

/-- A morphism from the scheme-theoretic closure to the quotient spectrum is uniquely
determined by compatibility with their closed immersions into the affine spectrum. -/
theorem schemeTheoreticClosureIso_unique (f : Fin n → A)
    (g : schemeTheoreticClosure (union f) ⟶
      Spec (CommRingCat.of (A ⧸ closureIdeal f)))
    (hg : g ≫ Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (closureIdeal f))) =
        schemeTheoreticClosureι (union f)) :
    g = (schemeTheoreticClosureIso f).hom := by
  let q : Spec (CommRingCat.of (A ⧸ closureIdeal f)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (closureIdeal f)))
  let hqClosed : IsClosedImmersion q := by
    dsimp only [q]
    exact IsClosedImmersion.spec_of_quotient_mk
      (R := CommRingCat.of A) (closureIdeal f)
  let hqMono : Mono q :=
    @SurjectiveOnStalks.mono_of_injective _ _ q hqClosed.toSurjectiveOnStalks
      hqClosed.isClosedEmbedding.injective
  exact hqMono.right_cancellation _ _ (by
    dsimp only [q]
    rw [hg, schemeTheoreticClosureIso_hom_comp_quotientMap])

/-- The inclusion of a finite union of principal opens into an affine spectrum is
quasi-compact. -/
instance quasiCompact_ι (f : Fin n → A) : QuasiCompact (union f).ι := sorry

/-- A finite union of principal opens is scheme-theoretically dense exactly when the kernel
of the map to the product of the principal localizations is the zero ideal. -/
theorem schemeTheoreticallyDense_iff_closureIdeal_eq_bot (f : Fin n → A) :
    schemeTheoreticallyDense (union f) ↔ closureIdeal f = ⊥ := sorry

end

end AlgebraicGeometry.Spec.BasicOpenUnion
