/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.FromSections

/-!
# Morphism data for projective spectra

A positive-degree Veronese section map to the section ring of an invertible module determines
a morphism to a projective spectrum. This file packages such data and compares presentations
after passage to common multiples of their degrees.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A positive-degree Veronese section map into the tensor-power section ring of an invertible
module, together with its grading and generation properties. -/
structure MorphismDatum (T : Scheme.{u}) where
  /-- The positive degree indexing the Veronese ring. -/
  degree : ℕ
  /-- Positivity of the Veronese degree. -/
  positive : 1 ≤ degree
  /-- The invertible module on the source scheme. -/
  lineBundle : T.Modules
  /-- Invertibility of the chosen module. -/
  lineBundle_invertible : Scheme.Modules.Invertible lineBundle
  /-- The homomorphism from the Veronese ring to the tensor-power section ring. -/
  sectionMap :
    GradedRing.Veronese 𝒜 degree →+* RingedSpace.GradedSections.ring lineBundle
  /-- The section map preserves the Veronese grading. -/
  preservesDegree :
    veroneseSectionMapPreservesDegree 𝒜 degree lineBundle sectionMap
  /-- The degree-one image of the section map generates the invertible module. -/
  generates :
    @veroneseDegreeOneImageGenerates A σ _ _ _ 𝒜 _ T degree lineBundle
      lineBundle_invertible sectionMap

namespace MorphismDatum

variable {T : Scheme.{u}}

/-- Construct a projective-spectrum morphism datum from a positive Veronese degree, an
invertible module, and a grading-preserving section map whose degree-one image generates. -/
def ofVeroneseSectionMap
    (degree : ℕ) (positive : 1 ≤ degree) (lineBundle : T.Modules)
    (lineBundle_invertible : Scheme.Modules.Invertible lineBundle)
    (sectionMap :
      GradedRing.Veronese 𝒜 degree →+* RingedSpace.GradedSections.ring lineBundle)
    (preservesDegree :
      veroneseSectionMapPreservesDegree 𝒜 degree lineBundle sectionMap)
    (generates :
      @veroneseDegreeOneImageGenerates A σ _ _ _ 𝒜 _ T degree lineBundle
        lineBundle_invertible sectionMap) :
    MorphismDatum 𝒜 T where
  degree := degree
  positive := positive
  lineBundle := lineBundle
  lineBundle_invertible := lineBundle_invertible
  sectionMap := sectionMap
  preservesDegree := preservesDegree
  generates := generates

/-- The positivity, invertibility, grading, and generation conditions carried by a
projective-spectrum morphism datum hold simultaneously. -/
theorem conditions_spec (tau : MorphismDatum 𝒜 T) :
    1 ≤ tau.degree ∧
      Scheme.Modules.Invertible tau.lineBundle ∧
      veroneseSectionMapPreservesDegree 𝒜 tau.degree tau.lineBundle tau.sectionMap ∧
      @veroneseDegreeOneImageGenerates A σ _ _ _ 𝒜 _ T tau.degree tau.lineBundle
        tau.lineBundle_invertible tau.sectionMap :=
  ⟨tau.positive, tau.lineBundle_invertible, tau.preservesDegree, tau.generates⟩

/-- Include a homogeneous piece of degree `m * n` into the Veronese ring at the component
`m * a`, where `n = a * tau.degree`. -/
noncomputable def commonMultipleInputMap
    (tau : MorphismDatum 𝒜 T) (n a : ℕ) (hn : n = a * tau.degree) (m : ℕ) :
    AddCommGrpCat.of (𝒜 (m * n)) ⟶ AddCommGrpCat.of (GradedRing.Veronese 𝒜 tau.degree) :=
  AddCommGrpCat.ofHom <|
    (DirectSum.of (fun k : ℕ ↦ (𝒜 (k * tau.degree) : Type u)) (m * a)).comp
      (AddEquiv.toAddMonoidHom <| AddEquiv.cast (M := fun i : ℕ ↦ (𝒜 i : Type u)) <|
        (congrArg (fun t : ℕ ↦ m * t) hn).trans (Nat.mul_assoc m a tau.degree).symm)

/-- Restrict a Veronese section map to one homogeneous degree at a common multiple and
transport its value to the corresponding tensor power of the powered line bundle. -/
noncomputable def commonMultipleDegreeMap
    (tau : MorphismDatum 𝒜 T) (n a : ℕ) (hn : n = a * tau.degree) (m : ℕ) :
    AddCommGrpCat.of (𝒜 (m * n)) ⟶
      AddCommGrpCat.of
        (RingedSpace.GradedSections.degree
          (RingedSpace.TensorPower.sheaf tau.lineBundle a) m) :=
  commonMultipleInputMap 𝒜 tau n a hn m ≫
    AddCommGrpCat.ofHom tau.sectionMap.toAddMonoidHom ≫
      AddCommGrpCat.ofHom
        (DirectSum.component ℤ ℕ
          (fun k : ℕ ↦ RingedSpace.GradedSections.degree tau.lineBundle k)
          (m * a)).toAddMonoidHom ≫
        Scheme.Modules.globalSectionsMap
          (RingedSpace.TensorPower.mulIso tau.lineBundle a m).inv

/-- A morphism to a projective spectrum is associated to a datum when it factors through the
datum's positive-degree open and the factorization is compatible with its section map. -/
def AssociatedTo (tau : MorphismDatum 𝒜 T) (phi : T ⟶ Proj 𝒜) : Prop :=
  ∃ phiDegree : T ⟶ (Proj.degreeOpen 𝒜 tau.degree).toScheme,
    phiDegree ≫ (Proj.degreeOpen 𝒜 tau.degree).ι = phi ∧
      @degreeOpenTwistCompatibility A σ _ _ _ 𝒜 _ T tau.degree tau.lineBundle
        tau.lineBundle_invertible tau.sectionMap phiDegree

/-- Association with a projective-spectrum morphism is characterized by a compatible
factorization through the datum's positive-degree open. -/
theorem associatedTo_iff (tau : MorphismDatum 𝒜 T) (phi : T ⟶ Proj 𝒜) :
    AssociatedTo 𝒜 tau phi ↔
      ∃ phiDegree : T ⟶ (Proj.degreeOpen 𝒜 tau.degree).toScheme,
        phiDegree ≫ (Proj.degreeOpen 𝒜 tau.degree).ι = phi ∧
          @degreeOpenTwistCompatibility A σ _ _ _ 𝒜 _ T tau.degree tau.lineBundle
            tau.lineBundle_invertible tau.sectionMap phiDegree :=
  Iff.rfl

/-- Two morphism data are compatible at a specified common multiple when an isomorphism of
the corresponding tensor powers identifies every restricted homogeneous degree map. -/
def CompatibleAt (tau tau' : MorphismDatum 𝒜 T) (n a a' : ℕ)
    (hn : n = a * tau.degree) (hn' : n = a' * tau'.degree) : Prop :=
  ∃ beta : RingedSpace.TensorPower.sheaf tau.lineBundle a ≅
      RingedSpace.TensorPower.sheaf tau'.lineBundle a',
    ∀ m,
      commonMultipleDegreeMap 𝒜 tau n a hn m ≫
          Scheme.Modules.globalSectionsMap (RingedSpace.TensorPower.mapIso beta m).hom =
        commonMultipleDegreeMap 𝒜 tau' n a' hn' m

/-- Compatibility at a specified common multiple is characterized by an isomorphism of the
corresponding tensor powers that identifies all restricted homogeneous maps. -/
theorem compatibleAt_iff (tau tau' : MorphismDatum 𝒜 T) (n a a' : ℕ)
    (hn : n = a * tau.degree) (hn' : n = a' * tau'.degree) :
    CompatibleAt 𝒜 tau tau' n a a' hn hn' ↔
      ∃ beta : RingedSpace.TensorPower.sheaf tau.lineBundle a ≅
          RingedSpace.TensorPower.sheaf tau'.lineBundle a',
        ∀ m,
          commonMultipleDegreeMap 𝒜 tau n a hn m ≫
              Scheme.Modules.globalSectionsMap (RingedSpace.TensorPower.mapIso beta m).hom =
            commonMultipleDegreeMap 𝒜 tau' n a' hn' m :=
  Iff.rfl

/-- Two morphism data are compatible at the least common multiple of their degrees. -/
def CompatibleAtLcm (tau tau' : MorphismDatum 𝒜 T) : Prop :=
  ∃ a a',
    ∃ hn : Nat.lcm tau.degree tau'.degree = a * tau.degree,
      ∃ hn' : Nat.lcm tau.degree tau'.degree = a' * tau'.degree,
        CompatibleAt 𝒜 tau tau' (Nat.lcm tau.degree tau'.degree) a a' hn hn'

/-- Two morphism data are equivalent when they are compatible at the product of their degrees,
using the opposite degree as the tensor exponent on each line bundle. -/
def Equivalent (tau tau' : MorphismDatum 𝒜 T) : Prop :=
  CompatibleAt 𝒜 tau tau' (tau.degree * tau'.degree) tau'.degree tau.degree
    (Nat.mul_comm tau.degree tau'.degree) rfl

/-- Two morphism data are compatible at some common multiple when there is a positive degree
that is a multiple of both degrees and at which their restricted maps are compatible. -/
def SomeCommonMultipleCompatible (tau tau' : MorphismDatum 𝒜 T) : Prop :=
  ∃ n a a', 0 < n ∧
    ∃ hn : n = a * tau.degree,
      ∃ hn' : n = a' * tau'.degree,
        CompatibleAt 𝒜 tau tau' n a a' hn hn'

/-- A projective-spectrum morphism datum has a unique associated morphism. -/
theorem existsUniqueAssociatedMorphism (tau : MorphismDatum 𝒜 T) :
    ∃! phi : T ⟶ Proj 𝒜, AssociatedTo 𝒜 tau phi := sorry

/-- Compatibility at the least common multiple is equivalent to compatibility at the fixed
product of the two degrees. -/
theorem compatibleAtLcm_iff_equivalent (tau tau' : MorphismDatum 𝒜 T) :
    CompatibleAtLcm 𝒜 tau tau' ↔ Equivalent 𝒜 tau tau' := sorry

/-- Compatibility at the fixed product of two positive degrees is equivalent to compatibility
at some positive common multiple. -/
theorem equivalent_iff_someCommonMultipleCompatible (tau tau' : MorphismDatum 𝒜 T) :
    Equivalent 𝒜 tau tau' ↔ SomeCommonMultipleCompatible 𝒜 tau tau' := sorry

/-- Two morphism data are equivalent exactly when associated morphisms arising from them are
equal. -/
theorem equivalent_iff_eq_associatedMorphism
    (tau tau' : MorphismDatum 𝒜 T) {phi phi' : T ⟶ Proj 𝒜}
    (hphi : AssociatedTo 𝒜 tau phi) (hphi' : AssociatedTo 𝒜 tau' phi') :
    Equivalent 𝒜 tau tau' ↔ phi = phi' := sorry

/-- Least-common-multiple compatibility, fixed-product equivalence, compatibility at some
positive common multiple, and equality of associated morphisms are equivalent. -/
theorem equivalent_tfae
    (tau tau' : MorphismDatum 𝒜 T) {phi phi' : T ⟶ Proj 𝒜}
    (hphi : AssociatedTo 𝒜 tau phi) (hphi' : AssociatedTo 𝒜 tau' phi') :
    List.TFAE [
      CompatibleAtLcm 𝒜 tau tau',
      Equivalent 𝒜 tau tau',
      SomeCommonMultipleCompatible 𝒜 tau tau',
      phi = phi'
    ] := sorry

end MorphismDatum

/-- An invertible module equipped with a degree-preserving homomorphism from the degree-one
Veronese ring whose degree-one image generates the module. -/
structure DegreeOneMorphismDatum (T : Scheme.{u}) where
  /-- The invertible module on the source scheme. -/
  lineBundle : T.Modules
  /-- Invertibility of the chosen module. -/
  lineBundle_invertible : Scheme.Modules.Invertible lineBundle
  /-- The homomorphism from the degree-one Veronese ring to the tensor-power section ring. -/
  sectionMap :
    GradedRing.Veronese 𝒜 1 →+* RingedSpace.GradedSections.ring lineBundle
  /-- The section map preserves the grading. -/
  preservesDegree : veroneseSectionMapPreservesDegree 𝒜 1 lineBundle sectionMap
  /-- The degree-one image of the section map generates the invertible module. -/
  generates :
    @veroneseDegreeOneImageGenerates A σ _ _ _ 𝒜 _ T 1 lineBundle
      lineBundle_invertible sectionMap

namespace DegreeOneMorphismDatum

variable {T : Scheme.{u}}

/-- Construct degree-one morphism data from an invertible module and a degree-preserving section
map whose degree-one image generates. -/
def ofVeroneseSectionMap
    (lineBundle : T.Modules)
    (lineBundle_invertible : Scheme.Modules.Invertible lineBundle)
    (sectionMap :
      GradedRing.Veronese 𝒜 1 →+* RingedSpace.GradedSections.ring lineBundle)
    (preservesDegree : veroneseSectionMapPreservesDegree 𝒜 1 lineBundle sectionMap)
    (generates :
      @veroneseDegreeOneImageGenerates A σ _ _ _ 𝒜 _ T 1 lineBundle
        lineBundle_invertible sectionMap) :
    DegreeOneMorphismDatum 𝒜 T where
  lineBundle := lineBundle
  lineBundle_invertible := lineBundle_invertible
  sectionMap := sectionMap
  preservesDegree := preservesDegree
  generates := generates

/-- The invertibility, grading, and generation conditions of degree-one morphism data hold
simultaneously. -/
theorem conditions_spec (tau : DegreeOneMorphismDatum 𝒜 T) :
    Scheme.Modules.Invertible tau.lineBundle ∧
      veroneseSectionMapPreservesDegree 𝒜 1 tau.lineBundle tau.sectionMap ∧
      @veroneseDegreeOneImageGenerates A σ _ _ _ 𝒜 _ T 1 tau.lineBundle
        tau.lineBundle_invertible tau.sectionMap :=
  ⟨tau.lineBundle_invertible, tau.preservesDegree, tau.generates⟩

/-- Regard degree-one morphism data as positive-degree morphism data of degree one. -/
def toMorphismDatum (tau : DegreeOneMorphismDatum 𝒜 T) : MorphismDatum 𝒜 T :=
  MorphismDatum.ofVeroneseSectionMap 𝒜 1 (Nat.le_refl 1) tau.lineBundle
    tau.lineBundle_invertible tau.sectionMap tau.preservesDegree tau.generates

/-- The map induced by the section-ring homomorphism on one homogeneous degree. -/
noncomputable def degreeMap (tau : DegreeOneMorphismDatum 𝒜 T) (n : ℕ) :
    AddCommGrpCat.of (𝒜 n) ⟶
      AddCommGrpCat.of (RingedSpace.GradedSections.degree tau.lineBundle n) :=
  AddCommGrpCat.ofHom <|
    (DirectSum.component ℤ ℕ
      (fun k : ℕ ↦ RingedSpace.GradedSections.degree tau.lineBundle k)
      n).toAddMonoidHom.comp <|
      tau.sectionMap.toAddMonoidHom.comp <|
        (DirectSum.of (fun k : ℕ ↦ (𝒜 (k * 1) : Type u)) n).comp
          (AddEquiv.toAddMonoidHom <| AddEquiv.cast
            (M := fun k : ℕ ↦ (𝒜 k : Type u)) (Nat.mul_one n).symm)

/-- Two degree-one data are strictly equivalent when an isomorphism of their invertible modules
identifies their maps on every homogeneous degree. -/
def Equivalent (tau tau' : DegreeOneMorphismDatum 𝒜 T) : Prop :=
  ∃ beta : tau.lineBundle ≅ tau'.lineBundle,
    ∀ n,
      degreeMap 𝒜 tau n ≫
          Scheme.Modules.globalSectionsMap (RingedSpace.TensorPower.mapIso beta n).hom =
        degreeMap 𝒜 tau' n

/-- Strict equivalence of degree-one data agrees with equivalence of the corresponding general
morphism data. -/
theorem equivalent_iff_toMorphismDatum_equivalent
    (tau tau' : DegreeOneMorphismDatum 𝒜 T) :
    Equivalent 𝒜 tau tau' ↔
      MorphismDatum.Equivalent 𝒜 tau.toMorphismDatum tau'.toMorphismDatum := sorry

/-- Strict equivalence of degree-one morphism data is reflexive. -/
theorem equivalent_refl (tau : DegreeOneMorphismDatum 𝒜 T) :
    Equivalent 𝒜 tau tau := sorry

/-- Strict equivalence of degree-one morphism data is symmetric. -/
theorem equivalent_symm {tau tau' : DegreeOneMorphismDatum 𝒜 T} :
    Equivalent 𝒜 tau tau' → Equivalent 𝒜 tau' tau := sorry

/-- Strict equivalence of degree-one morphism data is transitive. -/
theorem equivalent_trans {tau tau' tau'' : DegreeOneMorphismDatum 𝒜 T} :
    Equivalent 𝒜 tau tau' → Equivalent 𝒜 tau' tau'' → Equivalent 𝒜 tau tau'' := sorry

/-- The canonical setoid of degree-one morphism data under strict equivalence. -/
def setoid (T : Scheme.{u}) : Setoid (DegreeOneMorphismDatum 𝒜 T) where
  r := Equivalent 𝒜
  iseqv := ⟨equivalent_refl 𝒜, equivalent_symm 𝒜, equivalent_trans 𝒜⟩

/-- A projective-spectrum morphism is associated to degree-one data when it is associated to the
corresponding general morphism data. -/
def AssociatedTo (tau : DegreeOneMorphismDatum 𝒜 T) (phi : T ⟶ Proj 𝒜) : Prop :=
  MorphismDatum.AssociatedTo 𝒜 tau.toMorphismDatum phi

/-- Association of degree-one data unfolds to association of the corresponding general morphism
data. -/
theorem associatedTo_iff (tau : DegreeOneMorphismDatum 𝒜 T) (phi : T ⟶ Proj 𝒜) :
    AssociatedTo 𝒜 tau phi ↔ MorphismDatum.AssociatedTo 𝒜 tau.toMorphismDatum phi :=
  Iff.rfl

/-- Strictly equivalent degree-one data have the same associated projective-spectrum morphisms. -/
theorem equivalent_iff_associatedTo_iff
    {tau tau' : DegreeOneMorphismDatum 𝒜 T} (htau : Equivalent 𝒜 tau tau')
    (phi : T ⟶ Proj 𝒜) :
    AssociatedTo 𝒜 tau phi ↔ AssociatedTo 𝒜 tau' phi := sorry

/-- Strict equivalence of degree-one data is equivalent to equality of associated morphisms. -/
theorem equivalent_iff_eq_associatedMorphism
    (tau tau' : DegreeOneMorphismDatum 𝒜 T) {phi phi' : T ⟶ Proj 𝒜}
    (hphi : AssociatedTo 𝒜 tau phi) (hphi' : AssociatedTo 𝒜 tau' phi') :
    Equivalent 𝒜 tau tau' ↔ phi = phi' := sorry

end DegreeOneMorphismDatum

/-- Strict-equivalence classes of degree-one morphism data. -/
abbrev DegreeOneMorphismDatumClass (T : Scheme.{u}) : Type (u + 1) :=
  _root_.Quotient (DegreeOneMorphismDatum.setoid 𝒜 T)

namespace DegreeOneMorphismDatumClass

variable {T : Scheme.{u}}

/-- Association of a strict-equivalence class with a projective-spectrum morphism. -/
def AssociatedTo (tau : DegreeOneMorphismDatumClass 𝒜 T) (phi : T ⟶ Proj 𝒜) : Prop :=
  Quotient.liftOn tau (fun tau' ↦ DegreeOneMorphismDatum.AssociatedTo 𝒜 tau' phi)
    fun _ _ htau ↦ propext
      (DegreeOneMorphismDatum.equivalent_iff_associatedTo_iff 𝒜 htau phi)

/-- Association of a quotient class represented by degree-one data is association of that
representative. -/
theorem associatedTo_mk_iff (tau : DegreeOneMorphismDatum 𝒜 T) (phi : T ⟶ Proj 𝒜) :
    AssociatedTo 𝒜 (⟦tau⟧ : DegreeOneMorphismDatumClass 𝒜 T) phi ↔
      DegreeOneMorphismDatum.AssociatedTo 𝒜 tau phi := sorry

/-- Every strict-equivalence class of degree-one data has a unique associated morphism to the
projective spectrum. -/
theorem existsUniqueAssociatedMorphism (tau : DegreeOneMorphismDatumClass 𝒜 T) :
    ∃! phi : T ⟶ Proj 𝒜, AssociatedTo 𝒜 tau phi := sorry

/-- If the graded ring is generated in degree one, every morphism to its projective spectrum has
a unique associated strict-equivalence class of degree-one data. -/
theorem existsUniqueOfMorphism (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1)
    (phi : T ⟶ Proj 𝒜) :
    ∃! tau : DegreeOneMorphismDatumClass 𝒜 T, AssociatedTo 𝒜 tau phi := sorry

/-- Under degree-one generation, strict-equivalence classes of degree-one data and morphisms to
the projective spectrum determine one another uniquely through association. -/
theorem associatedTo_bijective (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    (∀ tau : DegreeOneMorphismDatumClass 𝒜 T,
      ∃! phi : T ⟶ Proj 𝒜, AssociatedTo 𝒜 tau phi) ∧
    (∀ phi : T ⟶ Proj 𝒜,
      ∃! tau : DegreeOneMorphismDatumClass 𝒜 T, AssociatedTo 𝒜 tau phi) := sorry

end DegreeOneMorphismDatumClass

end AlgebraicGeometry.Proj
