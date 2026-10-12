/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.LinearEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Naive number of moduli of degree-`d` hypersurfaces

This module defines relative families, finite coverings by families, and the resulting
numerical invariant for hypersurfaces in projective space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface
namespace Moduli

/-- Relative projective `n`-space `P^n_V` is the pullback of `P^n_k ⟶ Spec k` along
the structure morphism `V ⟶ Spec k`. -/
def overProjectiveSpace {k : Type u} [Field k]
    (V : Over (Spec (CommRingCat.of k))) (n : ℕ) : Scheme.{u} :=
  pullback V.hom (ProjectiveSpace.toSpec k n)

/-- The structure morphism `P^n_V ⟶ V`. -/
def overProjectiveSpace_fst {k : Type u} [Field k]
    (V : Over (Spec (CommRingCat.of k))) (n : ℕ) :
    overProjectiveSpace V n ⟶ V.left :=
  pullback.fst V.hom (ProjectiveSpace.toSpec k n)

/-- The projection `P^n_V ⟶ P^n_k`. -/
def overProjectiveSpace_snd {k : Type u} [Field k]
    (V : Over (Spec (CommRingCat.of k))) (n : ℕ) :
    overProjectiveSpace V n ⟶ ProjectiveSpace.scheme k n :=
  pullback.snd V.hom (ProjectiveSpace.toSpec k n)

/-- A morphism from projective space over a residue field identifies that projective space
with the scheme-theoretic fibre of `P^n_V ⟶ V` when the associated square is cartesian. -/
def IsFibreOverResidueField {k : Type u} [Field k]
    (V : Over (Spec (CommRingCat.of k))) (n : ℕ) (v : V.left)
    (φ : ProjectiveSpace.scheme (V.left.residueField v) n ⟶ overProjectiveSpace V n) : Prop :=
  IsPullback φ (ProjectiveSpace.toSpec (V.left.residueField v) n)
    (overProjectiveSpace_fst V n) (V.left.fromSpecResidueField v)

/-- The fibre predicate is equivalent to the corresponding cartesian-square condition. -/
theorem isFibreOverResidueField_iff {k : Type u} [Field k]
    {V : Over (Spec (CommRingCat.of k))} {n : ℕ} {v : V.left}
    {φ : ProjectiveSpace.scheme (V.left.residueField v) n ⟶ overProjectiveSpace V n} :
    IsFibreOverResidueField V n v φ ↔
      IsPullback φ (ProjectiveSpace.toSpec (V.left.residueField v) n)
        (overProjectiveSpace_fst V n) (V.left.fromSpecResidueField v) := sorry

/-- A closed subscheme of `P^n_V` is a family of degree-`d` hypersurfaces if every
scheme-theoretic fibre is a degree-`d` hypersurface over its residue field. -/
def IsFamily {k : Type u} [Field k] (n d : ℕ)
    (V : Over (Spec (CommRingCat.of k)))
    (Z : (overProjectiveSpace V n).IdealSheafData) : Prop :=
  ∀ v : V.left,
    ∃ φ : ProjectiveSpace.scheme (V.left.residueField v) n ⟶ overProjectiveSpace V n,
      IsFibreOverResidueField V n v φ ∧ IsOfDegree n d (Z.comap φ)

/-- A family predicate is equivalent to the fibrewise existence of degree-`d` equations. -/
theorem isFamily_iff {k : Type u} [Field k] {n d : ℕ}
    {V : Over (Spec (CommRingCat.of k))} {Z : (overProjectiveSpace V n).IdealSheafData} :
    IsFamily n d V Z ↔
      ∀ v : V.left,
        ∃ φ : ProjectiveSpace.scheme (V.left.residueField v) n ⟶ overProjectiveSpace V n,
          IsFibreOverResidueField V n v φ ∧ IsOfDegree n d (Z.comap φ) := sorry

/-- Every fibre of a degree-`d` family is a degree-`d` hypersurface after a cartesian
identification of its projective ambient space. -/
theorem fibre_isOfDegree {k : Type u} [Field k] {n d : ℕ}
    {V : Over (Spec (CommRingCat.of k))} {Z : (overProjectiveSpace V n).IdealSheafData}
    (hZ : IsFamily n d V Z) (v : V.left) :
    ∃ φ : ProjectiveSpace.scheme (V.left.residueField v) n ⟶ overProjectiveSpace V n,
      IsFibreOverResidueField V n v φ ∧ IsOfDegree n d (Z.comap φ) := sorry

/-- The moduli problem of degree-`d` hypersurfaces in `P^n` admits a finite covering by
families over varieties of dimension at most `m`, with some base of dimension exactly `m`. -/
def AdmitsCovering (k : Type u) [Field k] [IsAlgClosed k] (n d m : ℕ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (_ : Nonempty ι)
      (V : ι → Over (Spec (CommRingCat.of k)))
      (X : (i : ι) → (overProjectiveSpace (V i) n).IdealSheafData),
    (∀ i, Variety (V i)) ∧
      (∀ i, IsFamily n d (V i) (X i)) ∧
        (∀ i, topologicalKrullDim (V i).left ≤ m) ∧
          (∃ i, topologicalKrullDim (V i).left = m) ∧
            ∀ (Z : (ProjectiveSpace.scheme k n).IdealSheafData),
              IsOfDegree n d Z →
                ∃ (i : ι) (σ : Spec (CommRingCat.of k) ⟶ (V i).left)
                    (φ : ProjectiveSpace.scheme k n ⟶ overProjectiveSpace (V i) n),
                  σ ≫ (V i).hom = 𝟙 (Spec (CommRingCat.of k)) ∧
                    φ ≫ overProjectiveSpace_fst (V i) n = ProjectiveSpace.toSpec k n ≫ σ ∧
                      φ ≫ overProjectiveSpace_snd (V i) n = 𝟙 (ProjectiveSpace.scheme k n) ∧
                        IsLinearEquivalent n d Z ((X i).comap φ)

/-- The covering predicate is equivalent to its finite family, dimension, and equivalence
conditions. -/
theorem admitsCovering_iff (k : Type u) [Field k] [IsAlgClosed k] {n d m : ℕ} :
    AdmitsCovering k n d m ↔
      ∃ (ι : Type u) (_ : Fintype ι) (_ : Nonempty ι)
          (V : ι → Over (Spec (CommRingCat.of k)))
          (X : (i : ι) → (overProjectiveSpace (V i) n).IdealSheafData),
        (∀ i, Variety (V i)) ∧
          (∀ i, IsFamily n d (V i) (X i)) ∧
            (∀ i, topologicalKrullDim (V i).left ≤ m) ∧
              (∃ i, topologicalKrullDim (V i).left = m) ∧
                ∀ (Z : (ProjectiveSpace.scheme k n).IdealSheafData),
                  IsOfDegree n d Z →
                    ∃ (i : ι) (σ : Spec (CommRingCat.of k) ⟶ (V i).left)
                        (φ : ProjectiveSpace.scheme k n ⟶ overProjectiveSpace (V i) n),
                      σ ≫ (V i).hom = 𝟙 (Spec (CommRingCat.of k)) ∧
                        φ ≫ overProjectiveSpace_fst (V i) n =
                            ProjectiveSpace.toSpec k n ≫ σ ∧
                          φ ≫ overProjectiveSpace_snd (V i) n =
                            𝟙 (ProjectiveSpace.scheme k n) ∧
                            IsLinearEquivalent n d Z ((X i).comap φ) := sorry

/-- The number of moduli is the least `m` such that finitely many families over varieties
of dimension at most `m` cover every degree-`d` hypersurface up to equivalence. -/
def HasNumberOfModuli (k : Type u) [Field k] [IsAlgClosed k] (n d m : ℕ) : Prop :=
  AdmitsCovering k n d m ∧ ∀ m' < m, ¬ AdmitsCovering k n d m'

/-- The moduli-number predicate is equivalent to covering at `m` and failure of every
strictly smaller dimension. -/
theorem hasNumberOfModuli_iff (k : Type u) [Field k] [IsAlgClosed k] {n d m : ℕ} :
    HasNumberOfModuli k n d m ↔
      AdmitsCovering k n d m ∧ ∀ m' < m, ¬ AdmitsCovering k n d m' := sorry

/-- Positive-degree hypersurfaces in `P^1` have number of moduli `d - 3`. -/
theorem hasNumberOfModuli_P1 {k : Type u} [Field k] [IsAlgClosed k] {d : ℕ} (hd : 1 ≤ d) :
    HasNumberOfModuli k 1 d (d - 3) := sorry

/-- Lines in `P^2` have number of moduli `0`. -/
theorem hasNumberOfModuli_planeLine {k : Type u} [Field k] [IsAlgClosed k] :
    HasNumberOfModuli k 2 1 0 := sorry

/-- Plane conics have number of moduli `0`. -/
theorem hasNumberOfModuli_planeConic {k : Type u} [Field k] [IsAlgClosed k] :
    HasNumberOfModuli k 2 2 0 := sorry

/-- Quadrics in `P^n` have number of moduli `0` for every positive `n`. -/
theorem hasNumberOfModuli_quadric {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n) :
    HasNumberOfModuli k n 2 0 := sorry

/-- Plane cubics have number of moduli `1`. -/
theorem hasNumberOfModuli_planeCubic {k : Type u} [Field k] [IsAlgClosed k] :
    HasNumberOfModuli k 2 3 1 := sorry

/-- Cubic surfaces in `P^3` have number of moduli `4`. -/
theorem hasNumberOfModuli_cubicSurface {k : Type u} [Field k] [IsAlgClosed k] :
    HasNumberOfModuli k 3 3 4 := sorry

/-- Plane quartics have number of moduli `6`. -/
theorem hasNumberOfModuli_planeQuartic {k : Type u} [Field k] [IsAlgClosed k] :
    HasNumberOfModuli k 2 4 6 := sorry

end Moduli
end AlgebraicGeometry.ProjectiveSpace.Hypersurface
