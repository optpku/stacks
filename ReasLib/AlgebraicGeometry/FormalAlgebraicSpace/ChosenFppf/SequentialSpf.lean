module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Filter.CountablyGenerated
public import ReasLib.RingTheory.Topology.SequentialQuotients
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
public import ReasLib.AlgebraicGeometry.FormalSpectrum.ChosenFppf

/-!
# Sequential formal spectra

Countable neighbourhood bases and sequential quotient limits characterize countably indexed
formal spectra on the full big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.IsAffineFormalAlgebraicSpace

variable {S : Scheme.{u}}
variable [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]

/-- A presheaf is countably indexed affine when it is isomorphic to the underlying presheaf of
a countably indexed affine formal algebraic space. -/
def IsCountablyIndexedAffinePresheaf
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ Y : Sheaf (full.bigTopology S) (Type (u + 1)),
    IsCountablyIndexedAffine Y ∧ Nonempty (X ≅ Y.obj)

/-- For a sheaf, the presheaf characterization of countably indexed affineness agrees with
the countably indexed affine sheaf property. -/
theorem isCountablyIndexedAffinePresheaf_iff
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (Y : Sheaf (full.bigTopology S) (Type (u + 1))) :
    IsCountablyIndexedAffinePresheaf Y.obj ↔ IsCountablyIndexedAffine Y :=
  sorry

/-- A presheaf is the formal spectrum of a weakly admissible topological ring over the base
with a countably generated neighbourhood filter at zero. -/
def isColimitOfCountablyGeneratedSpf
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (structureHomA : Spec (.of A) ⟶ S),
    (nhds (0 : A)).IsCountablyGenerated ∧
      Nonempty (X ≅ (FppfFormalSpectrum.spf A structureHomA).obj)

/-- A countably generated formal-spectrum presentation consists of a weakly admissible ring
over the base with countably generated zero-neighbourhoods and a formal-spectrum isomorphism. -/
theorem isColimitOfCountablyGeneratedSpf_iff
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfCountablyGeneratedSpf X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (structureHomA : Spec (.of A) ⟶ S),
        (nhds (0 : A)).IsCountablyGenerated ∧
          Nonempty (X ≅ (FppfFormalSpectrum.spf A structureHomA).obj) :=
  Iff.rfl

/-- A presheaf is the formal spectrum of a weakly admissible topological ring over the base
with a descending countable neighbourhood basis of weak ideals of definition. -/
def isColimitOfWeakIdealSequence
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (structureHomA : Spec (.of A) ⟶ S) (I : ℕ → Ideal A),
    (∀ n, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I n)) ∧
      (∀ n, I (n + 1) ≤ I n) ∧
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) ∧
      Nonempty (X ≅ (FppfFormalSpectrum.spf A structureHomA).obj)

/-- A weak-ideal sequence presentation consists of a weakly admissible ring over the base,
a descending neighbourhood basis of weak ideals of definition, and a formal-spectrum isomorphism. -/
theorem isColimitOfWeakIdealSequence_iff
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfWeakIdealSequence X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (structureHomA : Spec (.of A) ⟶ S) (I : ℕ → Ideal A),
        (∀ n, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I n)) ∧
          (∀ n, I (n + 1) ≤ I n) ∧
          (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) ∧
          Nonempty (X ≅ (FppfFormalSpectrum.spf A structureHomA).obj) :=
  Iff.rfl

/-- A presheaf is the formal spectrum of a complete separated topological ring over the base
with a descending open ideal neighbourhood basis and locally nilpotent successive quotients. -/
def isColimitOfCompleteLocallyNilpotentSequence
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : IsTopologicalRing A)
    (structureHomA : Spec (.of A) ⟶ S) (I : ℕ → Ideal A),
    T2Space A ∧
      @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) ∧
      (∀ n, IsOpen (I n : Set A)) ∧
      (∀ n, I (n + 1) ≤ I n) ∧
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) ∧
      (∀ n, ((I n).map (Ideal.Quotient.mk (I (n + 1)))).IsLocallyNilpotent) ∧
      Nonempty (X ≅ (colimit (FppfFormalSpectrum.affineThickenings A structureHomA ⋙
        full.bigAffineInclusion S ⋙
        (full.bigTopology S).sheafifiedRepresentableFunctor)).obj)

/-- A complete locally nilpotent presentation consists of a complete separated topological
ring over the base, a descending open ideal basis with locally nilpotent successive quotients,
and an isomorphism to the canonical quotient-spectrum colimit. -/
theorem isColimitOfCompleteLocallyNilpotentSequence_iff
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfCompleteLocallyNilpotentSequence X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsTopologicalRing A)
        (structureHomA : Spec (.of A) ⟶ S) (I : ℕ → Ideal A),
        T2Space A ∧
          @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) ∧
          (∀ n, IsOpen (I n : Set A)) ∧
          (∀ n, I (n + 1) ≤ I n) ∧
          (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) ∧
          (∀ n, ((I n).map (Ideal.Quotient.mk (I (n + 1)))).IsLocallyNilpotent) ∧
          Nonempty (X ≅ (colimit (FppfFormalSpectrum.affineThickenings A structureHomA ⋙
            full.bigAffineInclusion S ⋙
            (full.bigTopology S).sheafifiedRepresentableFunctor)).obj) :=
  Iff.rfl

/-- A presheaf is the formal spectrum of a sequential quotient inverse limit, with its limit
topology and canonical map from a ring over the base, whose successive ideal quotients are
locally nilpotent. -/
def isColimitOfQuotientInverseLimit
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (B : Type u) (_ : CommRing B) (J : ℕ → Ideal B)
    (hJ : ∀ n, J (n + 1) ≤ J n)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : IsTopologicalRing A)
    (π : ∀ n, A →+* B ⧸ J n) (ι : B →+* A)
    (structureHomB : Spec (.of B) ⟶ S) (structureHomA : Spec (.of A) ⟶ S),
    (∀ n, ((J n).map (Ideal.Quotient.mk (J (n + 1)))).IsLocallyNilpotent) ∧
      TopologicalRing.IsSequentialQuotientLimit J hJ π ∧
      (∀ n, (π n).comp ι = Ideal.Quotient.mk (J n)) ∧
      Spec.map (CommRingCat.ofHom ι) ≫ structureHomB = structureHomA ∧
      Nonempty (X ≅ (colimit (FppfFormalSpectrum.affineThickenings A structureHomA ⋙
        full.bigAffineInclusion S ⋙
        (full.bigTopology S).sheafifiedRepresentableFunctor)).obj)

/-- A quotient inverse-limit presentation consists of compatible quotient projections
realizing every compatible family uniquely, the induced limit topology, a compatible map from
the original ring over the base, locally nilpotent successive ideal quotients, and an isomorphism
to the canonical quotient-spectrum colimit. -/
theorem isColimitOfQuotientInverseLimit_iff
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfQuotientInverseLimit X ↔
      ∃ (B : Type u) (_ : CommRing B) (J : ℕ → Ideal B)
        (hJ : ∀ n, J (n + 1) ≤ J n)
        (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsTopologicalRing A)
        (π : ∀ n, A →+* B ⧸ J n) (ι : B →+* A)
        (structureHomB : Spec (.of B) ⟶ S) (structureHomA : Spec (.of A) ⟶ S),
        (∀ n, ((J n).map (Ideal.Quotient.mk (J (n + 1)))).IsLocallyNilpotent) ∧
          TopologicalRing.IsSequentialQuotientLimit J hJ π ∧
          (∀ n, (π n).comp ι = Ideal.Quotient.mk (J n)) ∧
          Spec.map (CommRingCat.ofHom ι) ≫ structureHomB = structureHomA ∧
          Nonempty (X ≅ (colimit (FppfFormalSpectrum.affineThickenings A structureHomA ⋙
            full.bigAffineInclusion S ⋙
            (full.bigTopology S).sheafifiedRepresentableFunctor)).obj) :=
  Iff.rfl

/-- For a presheaf on the big fppf site, countably indexed affineness is equivalent to the
four countable formal-spectrum presentations. -/
theorem tfae_spf
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    List.TFAE [IsCountablyIndexedAffinePresheaf X, isColimitOfCountablyGeneratedSpf X,
      isColimitOfWeakIdealSequence X, isColimitOfCompleteLocallyNilpotentSequence X,
      isColimitOfQuotientInverseLimit X] :=
  sorry

/-- Countably indexed affine presheaves are exactly the formal spectra of weakly admissible
rings over the base with countably generated neighbourhoods of zero. -/
theorem isCountablyIndexedAffine_iff_isColimitOfCountablyGeneratedSpf
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    IsCountablyIndexedAffinePresheaf X ↔ isColimitOfCountablyGeneratedSpf X := by
  have characterization := tfae_spf X
  sorry

/-- A countably generated weakly admissible formal-spectrum presentation is equivalent to
one with a descending countable basis of weak ideals of definition. -/
theorem isColimitOfCountablyGeneratedSpf_iff_isColimitOfWeakIdealSequence
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfCountablyGeneratedSpf X ↔ isColimitOfWeakIdealSequence X := by
  have characterization := tfae_spf X
  sorry

/-- A complete separated ring with a descending open ideal basis having locally nilpotent
successive quotients gives a quotient inverse-limit formal-spectrum presentation. -/
theorem quotientInverseLimit_of_completeSequence
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfCompleteLocallyNilpotentSequence X →
      isColimitOfQuotientInverseLimit X := by
  have characterization := tfae_spf X
  sorry

/-- A sequential quotient inverse-limit formal-spectrum presentation yields a weakly
admissible presentation with countably generated neighbourhoods of zero. -/
theorem isColimitOfCountablyGeneratedSpf_of_isColimitOfQuotientInverseLimit
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) :
    isColimitOfQuotientInverseLimit X → isColimitOfCountablyGeneratedSpf X := by
  have characterization := tfae_spf X
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
