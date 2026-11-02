/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Left.Torsion
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Category
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.TwistedSections
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.RingTheory.GradedAlgebra.PositiveGenerators
public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Serre quotients of finite graded modules

The two canonical Serre quotients are formed from the kernel of associated sheafification and,
under degree-one generation, from eventual high-degree torsion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj.Associated

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- 0BXE: The kernel of the associated module functor. -/
@[stacks 0BXE]
noncomputable abbrev irrelevant :
    ObjectProperty (GradedModule.Left.FG 𝒜 ℤ) :=
  (fgFunctor 𝒜).kernel

/-- The kernel definition of irrelevance says that its associated module sheaf is zero. -/
theorem irrelevant_iff_isZero (M : GradedModule.Left.FG 𝒜 ℤ) :
    irrelevant 𝒜 M ↔ IsZero ((fgFunctor 𝒜).obj M) := Iff.rfl

private theorem irrelevant_eq_coherentKernel [IsNoetherianRing A] :
    irrelevant 𝒜 = (exactFunctor 𝒜).obj.kernel := by
  ext M
  constructor
  · intro hM
    exact IsZero.of_full_of_faithful_of_isZero (SheafOfModules.isCoherent _).ι
      ((exactFunctor 𝒜).obj.obj M) hM
  · intro hM
    exact (SheafOfModules.isCoherent _).ι.map_isZero hM

/-- 0BXE: Irrelevant finite graded modules form a Serre class over a Noetherian graded ring. -/
@[stacks 0BXE]
instance irrelevantIsSerre [IsNoetherianRing A] : (irrelevant 𝒜).IsSerreClass := by
  rw [irrelevant_eq_coherentKernel 𝒜]
  infer_instance

/-- 0BXF: Irrelevance is contained in the kernel of coherent associated sheafification. -/
@[stacks 0BXF]
theorem irrelevant_le_coherentKernel [IsNoetherianRing A] :
    irrelevant 𝒜 ≤ (exactFunctor 𝒜).obj.kernel :=
  (irrelevant_eq_coherentKernel 𝒜).le

/-- A graded module is irrelevant for a positive generating family when its pieces in the
positive-generator period eventually vanish. -/
def IsIrrelevantFor (G : GradedAlgebra.PositiveGenerators 𝒜)
    (M : GradedModule.Left 𝒜 ℤ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, M.grading ((n * G.period : ℕ) : ℤ) = ⊥

/-- For finite graded modules, kernel irrelevance agrees with eventual vanishing along every
positive generating period. -/
theorem irrelevant_iff_isIrrelevantFor
    (G : GradedAlgebra.PositiveGenerators 𝒜) (M : GradedModule.Left.FG 𝒜 ℤ) :
    irrelevant 𝒜 M ↔ IsIrrelevantFor 𝒜 G M.obj := sorry

/-- Under the degree-one finite-type hypotheses, torsion and irrelevance are the same Serre
object property. -/
theorem torsion_eq_irrelevant [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    GradedModule.Left.torsion 𝒜 = irrelevant 𝒜 := by
  classical
  obtain ⟨s, hs, hdegree⟩ := GradedAlgebra.exists_finset_generated_by 𝒜 hgenerated
  let G : GradedAlgebra.PositiveGenerators 𝒜 :=
    { elems := s
      degree := fun _ ↦ 1
      generates := hs
      homogeneous := fun x ↦ hdegree x.1 x.2
      positive := fun _ ↦ Nat.zero_lt_one }
  have hperiod : G.period = 1 := by
    apply Nat.dvd_one.mp
    exact Finset.lcm_dvd (fun _ _ ↦ dvd_rfl)
  ext M
  rw [irrelevant_iff_isIrrelevantFor 𝒜 G M]
  change GradedModule.Left.IsTorsion M.obj ↔ IsIrrelevantFor 𝒜 G M.obj
  simp only [GradedModule.Left.IsTorsion, IsIrrelevantFor, hperiod, Nat.mul_one]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h
    refine Filter.eventually_atTop.2 ⟨b.toNat, fun n hn ↦ hb n ?_⟩
    omega
  · intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    refine Filter.eventually_atTop.2 ⟨(N : ℤ), fun n hn ↦ ?_⟩
    have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg N) hn
    simpa [Int.toNat_of_nonneg hn0] using hN n.toNat (by omega)

/-- Under the degree-one finite-type hypotheses, torsion objects are in the kernel of coherent
associated sheafification. -/
theorem torsion_le_kernel [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    GradedModule.Left.torsion 𝒜 ≤ (FiniteType.exactFunctor 𝒜).obj.kernel := by
  letI := Algebra.FiniteType.isNoetherianRing (𝒜 0) A
  rw [torsion_eq_irrelevant 𝒜 hgenerated]
  exact irrelevant_le_coherentKernel 𝒜

namespace Irrelevant

/-- 0BXF: The bundled exact functor from the irrelevant Serre quotient induced by coherent
associated sheafification. -/
@[stacks 0BXF]
noncomputable def quotientExactFunctor [IsNoetherianRing A] :
    (irrelevant 𝒜).isoModSerre.Localization ⥤ₑ RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  ObjectProperty.SerreClassLocalization.inducedExactFunctor (irrelevant 𝒜) (exactFunctor 𝒜)
    (irrelevant_le_coherentKernel 𝒜)

/-- 0BXF: The functor underlying the exact functor from the irrelevant Serre quotient. -/
@[stacks 0BXF]
noncomputable abbrev quotientFunctor [IsNoetherianRing A] :
    (irrelevant 𝒜).isoModSerre.Localization ⥤ RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  (quotientExactFunctor 𝒜).obj

/-- 0BXF: Twisted sections followed by the canonical quotient form a quasi-inverse candidate
from coherent sheaves to the irrelevant Serre quotient. -/
@[stacks 0BXF]
noncomputable def quasiInverse [IsNoetherianRing A] :
    RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ (irrelevant 𝒜).isoModSerre.Localization :=
  Proj.TwistedSections.Nonnegative.fgFunctor 𝒜 ⋙ (irrelevant 𝒜).isoModSerre.Q

/-- 0BXF: The quotient associated-sheaf functor and twisted-sections quotient functor are
quasi-inverse. -/
@[stacks 0BXF]
theorem isQuasiInverse [IsNoetherianRing A] :
    (quotientFunctor 𝒜).IsQuasiInverse (quasiInverse 𝒜) := sorry

/-- 0BXF: The canonical functor from the irrelevant Serre quotient to coherent sheaves is an
equivalence. -/
@[stacks 0BXF]
theorem isEquivalence [IsNoetherianRing A] : (quotientFunctor 𝒜).IsEquivalence :=
  (isQuasiInverse 𝒜).isEquivalence

end Irrelevant

namespace Torsion

/-- The Serre quotient by eventual high-degree torsion, with the Noetherian structure on A
supplied canonically by finite type over its degree-zero part 𝒜 0. -/
@[stacks 0BXD]
abbrev Quotient [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)] :=
  (@ObjectProperty.isoModSerre _ _
    (@GradedModule.Left.instFGAbelian ℕ _ _ ℤ _ _ ℤ _ A _ _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A))
    (GradedModule.Left.torsion 𝒜)
    (@GradedModule.Left.instTorsionIsSerreClass A _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A))).Localization

/-- 0BXD: The bundled exact functor from the torsion Serre quotient induced by coherent
associated sheafification. -/
@[stacks 0BXD]
noncomputable def quotientExactFunctor [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    Quotient 𝒜 ⥤ₑ
      RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  @ObjectProperty.SerreClassLocalization.inducedExactFunctor _ _
    (@GradedModule.Left.instFGAbelian ℕ _ _ ℤ _ _ ℤ _ A _ _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A))
    (GradedModule.Left.torsion 𝒜)
    (@GradedModule.Left.instTorsionIsSerreClass A _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A))
    _ _ _ (FiniteType.exactFunctor 𝒜) (torsion_le_kernel 𝒜 hgenerated)

/-- 0BXD: The functor underlying the exact functor from the torsion Serre quotient. -/
@[stacks 0BXD]
noncomputable abbrev quotientFunctor [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    Quotient 𝒜 ⥤
      RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  (quotientExactFunctor 𝒜 hgenerated).obj

/-- 0BXD: The canonical functor from finitely generated graded modules to the torsion
quotient. -/
@[stacks 0BXD]
noncomputable def toQuotient [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)] :
    GradedModule.Left.FG 𝒜 ℤ ⥤ Quotient 𝒜 :=
  (@ObjectProperty.isoModSerre _ _
    (@GradedModule.Left.instFGAbelian ℕ _ _ ℤ _ _ ℤ _ A _ _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A))
    (GradedModule.Left.torsion 𝒜)
    (@GradedModule.Left.instTorsionIsSerreClass A _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A))).Q

/-- 0BXD: Twisted sections followed by the canonical torsion quotient give the concrete
quasi-inverse candidate from coherent sheaves to `Quotient 𝒜`. -/
@[stacks 0BXD]
noncomputable def quasiInverse [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)] :
    RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ Quotient 𝒜 :=
  @Proj.TwistedSections.Nonnegative.fgFunctor A _ 𝒜 _
      (Algebra.FiniteType.isNoetherianRing (𝒜 0) A) ⋙ toQuotient 𝒜

/-- 0BXD: Under degree-one generation, the torsion-quotient associated-sheaf functor and its
twisted-sections quotient functor are quasi-inverse. -/
@[stacks 0BXD]
theorem isQuasiInverse [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    (quotientFunctor 𝒜 hgenerated).IsQuasiInverse (quasiInverse 𝒜) := by
  letI := Algebra.FiniteType.isNoetherianRing (𝒜 0) A
  have htransport (P : ObjectProperty (GradedModule.Left.FG 𝒜 ℤ)) [P.IsSerreClass]
      (hPker : P ≤ (exactFunctor 𝒜).obj.kernel) (hP : P = irrelevant 𝒜) :
      (ObjectProperty.SerreClassLocalization.inducedExactFunctor P
        (exactFunctor 𝒜) hPker).obj.IsQuasiInverse
          (Proj.TwistedSections.Nonnegative.fgFunctor 𝒜 ⋙ P.isoModSerre.Q) := by
    subst P
    exact Irrelevant.isQuasiInverse 𝒜
  exact htransport _ (torsion_le_kernel 𝒜 hgenerated) (torsion_eq_irrelevant 𝒜 hgenerated)

/-- 0BXD: The canonical functor from the torsion Serre quotient to coherent sheaves is an
equivalence. -/
@[stacks 0BXD]
theorem isEquivalence [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) :
    (quotientFunctor 𝒜 hgenerated).IsEquivalence :=
  (isQuasiInverse 𝒜 hgenerated).isEquivalence

end Torsion

end AlgebraicGeometry.Proj.Associated
