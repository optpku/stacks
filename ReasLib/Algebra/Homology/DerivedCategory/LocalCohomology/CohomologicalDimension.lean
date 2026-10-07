module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.RingTheory.Ideal.FiniteGeneration.Family

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A]

/-- An integer `d ≥ -1` bounds the local cohomology of the regular `A`-module with
support in `I` if every right-adjoint presentation of local cohomology sends `A[0]`
to an object of `DerivedCategory.IsLE d`. -/
def HasDimensionLE (I : Ideal A) (d : ℤ) : Prop :=
  -1 ≤ d ∧
    ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤
        DerivedCategory.IdealPowerTorsion I)
      (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ),
      (RΓ.obj (ModuleCat.single0 (ModuleCat.of A A))).obj.IsLE d

/-- The defining characterization of a local-cohomological dimension bound. -/
theorem hasDimensionLE_iff (I : Ideal A) (d : ℤ) :
    HasDimensionLE I d ↔
      -1 ≤ d ∧
        ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤
            DerivedCategory.IdealPowerTorsion I)
          (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ),
          (RΓ.obj (ModuleCat.single0 (ModuleCat.of A A))).obj.IsLE d := sorry

/-- Increasing an integer bound preserves the local-cohomological dimension bound. -/
theorem HasDimensionLE.mono {I : Ideal A} {d e : ℤ} (h : HasDimensionLE I d)
    (hde : d ≤ e) :
    HasDimensionLE I e := sorry

/-- A finitely generated ideal has some integer local-cohomological dimension bound. -/
theorem exists_hasDimensionLE (I : Ideal A) (hI : I.FG) :
    ∃ d : ℤ, HasDimensionLE I d := sorry

/-- The local-cohomological dimension of a finitely generated ideal is its least
admissible integer bound. -/
noncomputable def dimension (I : Ideal A) (hI : I.FG) : ℤ :=
  sInf {d : ℤ | HasDimensionLE I d}

/-- The local-cohomological dimension is itself an admissible bound. -/
theorem dimension_spec (I : Ideal A) (hI : I.FG) :
    HasDimensionLE I (dimension I hI) := sorry

/-- An integer bounds local cohomology exactly when it is at least the
local-cohomological dimension. -/
theorem dimension_le_iff (I : Ideal A) (hI : I.FG) (d : ℤ) :
    dimension I hI ≤ d ↔ HasDimensionLE I d := sorry

/-- The local-cohomological dimension of the sum of two finitely generated ideals
is at most the sum of their local-cohomological dimensions. -/
theorem dimension_sup_le (I J : Ideal A) (hI : I.FG) (hJ : J.FG) :
    dimension (I ⊔ J) (Submodule.FG.sup hI hJ) ≤ dimension I hI + dimension J hJ := sorry

variable {B : Type u} [CommRing B]

/-- Extension of a finitely generated ideal along a ring homomorphism preserves every
local-cohomological dimension bound. -/
theorem HasDimensionLE.map (f : A →+* B) {I : Ideal A} (hI : I.FG) {d : ℤ}
    (h : HasDimensionLE I d) :
    HasDimensionLE (I.map f) d := sorry

/-- Faithfully flat extension preserves and reflects every local-cohomological dimension
bound of a finitely generated ideal. -/
theorem HasDimensionLE.map_iff_of_faithfullyFlat (f : A →+* B) {I : Ideal A}
    (hI : I.FG) (hf : f.FaithfullyFlat) (d : ℤ) :
    HasDimensionLE (I.map f) d ↔ HasDimensionLE I d := sorry

/-- Extending a finitely generated ideal along a ring homomorphism cannot increase its
local-cohomological dimension. -/
theorem dimension_map_le (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    dimension (I.map f) (hI.map f) ≤ dimension I hI := sorry

/-- Faithfully flat extension preserves the local-cohomological dimension of a finitely
generated ideal. -/
theorem dimension_map_eq_of_faithfullyFlat (f : A →+* B) (I : Ideal A)
    (hI : I.FG) (hf : f.FaithfullyFlat) :
    dimension (I.map f) (hI.map f) = dimension I hI := sorry

/-- The local-cohomological dimension of a finitely generated ideal is at most the
cardinality of any chosen finite generating family. -/
theorem dimension_le_generatorCount {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (G : I.FiniteGeneratingFamily) :
    dimension I hI ≤ (G.count : ℤ) := sorry

/-- If `r` elements define the same zero locus as a finitely generated ideal, then its
local-cohomological dimension is at most `r`. -/
theorem dimension_le_of_zeroLocus_eq {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A)
    (hV : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set A) =
      PrimeSpectrum.zeroLocus (I : Set A)) :
    dimension I hI ≤ (r : ℤ) := sorry

/-- If `Spec A ∖ V(I)` has an affine-open cover indexed by `Fin c`, then the
local-cohomological dimension of `I` is at most `c`. -/
theorem dimension_le_of_complement_hasCard {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {c : ℕ}
    (hcover : AffineOpenCover.HasCard (idealComplementOpens I).toScheme c) :
    dimension I hI ≤ (c : ℤ) := sorry

end Ideal.LocalCohomology
