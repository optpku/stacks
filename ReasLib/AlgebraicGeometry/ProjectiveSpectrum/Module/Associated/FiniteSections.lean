/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.CoherentCohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.GradedSections.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Category
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.EventualSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.ShiftComparison
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.ShiftedSections.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.TwistedSections.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.CategoryTheory.Sites.Cohomology.Zero
public import ReasLib.RingTheory.GradedAlgebra.PositiveGenerators
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite sections of associated module sheaves

This module relates the homogeneous pieces of an internally graded module to degree-zero
cohomology of its shifted associated sheaves. It also records the canonical maps between
truncated tensor-twist and shifted-associated-sheaf sections.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

namespace Proj.AssociatedModule.Presentation

variable {𝒜}
variable {Mpiece : ℤ → Type u} [∀ n : ℤ, AddCommGroup (Mpiece n)]

/-- The map from one homogeneous piece to degree-zero cohomology, obtained by transporting the
canonical section map across the degree-zero cohomology equivalence. -/
noncomputable def cohomologyZeroSectionMap
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece) (n : ℤ) :
    Mpiece n →+ (RingedSpace.moduleCohomology (P.associatedTwist n) 0 : Type u) :=
  (CategoryTheory.Sheaf.cohomologyZeroEquivSections
      (Opens.grothendieckTopology (Proj 𝒜).carrier)
      ((SheafOfModules.toSheaf (Proj 𝒜).toRingedSpace.ringCatSheaf).obj
        (P.associatedTwist n))
      (⊤ : (Proj 𝒜).Opens)).symm.toAddMonoidHom.comp (P.sectionMap n)

/-- The transported degree-zero cohomology map is the inverse cohomology equivalence applied to
the canonical section. -/
@[simp]
theorem cohomologyZeroSectionMap_apply
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece) (n : ℤ) (m : Mpiece n) :
    P.cohomologyZeroSectionMap n m =
      (CategoryTheory.Sheaf.cohomologyZeroEquivSections
        (Opens.grothendieckTopology (Proj 𝒜).carrier)
        ((SheafOfModules.toSheaf (Proj 𝒜).toRingedSpace.ringCatSheaf).obj
          (P.associatedTwist n))
        (⊤ : (Proj 𝒜).Opens)).symm (P.sectionMap n m) := rfl

end Proj.AssociatedModule.Presentation

namespace Proj.AssociatedModule.ShiftComparison.Truncated

/-- The additive comparison from truncated tensor-twist cohomology to truncated cohomology of
shifted associated sheaves. -/
@[stacks 0B5R "additive truncated comparison for associated-module twists"]
noncomputable def mapAdd [DirectSum.Decomposition ℳ]
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ) (k : ℤ) :
    Proj.TwistedSections.Cohomology.truncated 𝒜
        (Proj.AssociatedModule.sheaf 𝒜 ℳ) k →+
      Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k :=
  DirectSum.map fun n : {n : ℤ // k ≤ n} ↦
    (RingedSpace.moduleCohomologyMap (C.hom n.1) 0).hom

/-- The additive truncated comparison commutes with the full ambient `A`-action. -/
@[stacks 0B5R "linearity law for the truncated associated-module comparison"]
theorem map_smul [DirectSum.Decomposition ℳ]
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ) (k : ℤ)
    (a : A)
    (x : Proj.TwistedSections.Cohomology.truncated 𝒜
      (Proj.AssociatedModule.sheaf 𝒜 ℳ) k) :
    mapAdd 𝒜 ℳ C k (a • x) = a • mapAdd 𝒜 ℳ C k x := sorry

/-- The canonical linear comparison between the two lower-truncated cohomology modules. -/
@[stacks 0B5R "linear truncated comparison for associated-module twists"]
noncomputable def map [DirectSum.Decomposition ℳ]
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ) (k : ℤ) :
    Proj.TwistedSections.Cohomology.truncated 𝒜
        (Proj.AssociatedModule.sheaf 𝒜 ℳ) k →ₗ[A]
      Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k :=
  { mapAdd 𝒜 ℳ C k with
    map_smul' := map_smul 𝒜 ℳ C k }

/-- On a homogeneous summand, the truncated comparison is the degree-zero cohomology map induced
by the shift comparison in that degree. -/
@[simp, stacks 0B5R "truncated comparison on a homogeneous summand"]
theorem map_of [DirectSum.Decomposition ℳ]
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ) (k : ℤ)
    (n : {n : ℤ // k ≤ n})
    (x : Proj.TwistedSections.Cohomology.degree 𝒜
      (Proj.AssociatedModule.sheaf 𝒜 ℳ) n.1) :
    map 𝒜 ℳ C k
        (DirectSum.of
          (DirectSum.Gmodule.LowerBound.pieces k
            (Proj.TwistedSections.Cohomology.degree 𝒜
              (Proj.AssociatedModule.sheaf 𝒜 ℳ))) n x) =
      DirectSum.of
        (DirectSum.Gmodule.LowerBound.pieces k
          (Proj.AssociatedModule.ShiftedSections.Cohomology.degree 𝒜 ℳ)) n
        ((RingedSpace.moduleCohomologyMap (C.hom n.1) 0).hom x) := by
  exact DirectSum.map_of
    (fun n : {n : ℤ // k ≤ n} ↦
      (RingedSpace.moduleCohomologyMap (C.hom n.1) 0).hom) n x

/-- The canonical truncated comparison, with the canonical shift comparison inferred from
`𝒜` and `ℳ`. -/
@[stacks 0B5R "canonical truncated associated-module comparison"]
noncomputable def canonicalMap [DirectSum.Decomposition ℳ] (k : ℤ) :
    Proj.TwistedSections.Cohomology.truncated 𝒜
        (Proj.AssociatedModule.sheaf 𝒜 ℳ) k →ₗ[A]
      Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k :=
  map 𝒜 ℳ (Proj.AssociatedModule.ShiftComparison.canonical 𝒜 ℳ) k

/-- On a homogeneous summand, the canonical truncated comparison is induced by the canonical
shift-comparison morphism in that degree. -/
@[simp, stacks 0B5R "canonical truncated comparison on a homogeneous summand"]
theorem canonicalMap_of [DirectSum.Decomposition ℳ] (k : ℤ)
    (n : {n : ℤ // k ≤ n})
    (x : Proj.TwistedSections.Cohomology.degree 𝒜
      (Proj.AssociatedModule.sheaf 𝒜 ℳ) n.1) :
    canonicalMap 𝒜 ℳ k
        (DirectSum.of
          (DirectSum.Gmodule.LowerBound.pieces k
            (Proj.TwistedSections.Cohomology.degree 𝒜
              (Proj.AssociatedModule.sheaf 𝒜 ℳ))) n x) =
      DirectSum.of
        (DirectSum.Gmodule.LowerBound.pieces k
          (Proj.AssociatedModule.ShiftedSections.Cohomology.degree 𝒜 ℳ)) n
        ((RingedSpace.moduleCohomologyMap
          ((Proj.AssociatedModule.ShiftComparison.canonical 𝒜 ℳ).hom n.1) 0).hom x) :=
  map_of 𝒜 ℳ (Proj.AssociatedModule.ShiftComparison.canonical 𝒜 ℳ) k n x

end Proj.AssociatedModule.ShiftComparison.Truncated

namespace Proj.AssociatedModule.ShiftedSections.Truncated

/-- The additive map from an internally graded module to lower-truncated cohomology of its
shifted associated sheaves. -/
@[stacks 0B5R "additive truncated section map for shifted associated sheaves"]
noncomputable def mapAdd [DirectSum.Decomposition ℳ] (k : ℤ) :
    M →+ Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k :=
  (DirectSum.toAddMonoid fun n : ℤ ↦
    if h : k ≤ n then
      (DirectSum.of
        (DirectSum.Gmodule.LowerBound.pieces k
          (Proj.AssociatedModule.ShiftedSections.Cohomology.degree 𝒜 ℳ)) ⟨n, h⟩).comp
        ((Proj.AssociatedModule.ShiftedSections.presentation 𝒜 ℳ).cohomologyZeroSectionMap n)
    else 0).comp (DirectSum.decomposeAddEquiv ℳ).toAddMonoidHom

private theorem mapAdd_of [DirectSum.Decomposition ℳ] (k n : ℤ) (m : ℳ n) :
    mapAdd 𝒜 ℳ k (m : M) =
      if h : k ≤ n then
        DirectSum.of
          (DirectSum.Gmodule.LowerBound.pieces k (Cohomology.degree 𝒜 ℳ)) ⟨n, h⟩
          ((presentation 𝒜 ℳ).cohomologyZeroSectionMap n m)
      else 0 := by
  change (DirectSum.toAddMonoid _) (DirectSum.decompose ℳ (m : M)) = _
  rw [DirectSum.decompose_coe, DirectSum.toAddMonoid_of]
  split_ifs <;> rfl

private theorem cohomologyZeroSectionMap_smul [DirectSum.Decomposition ℳ]
    {d : ℕ} {n : ℤ} (a : 𝒜 d) (m : ℳ n) :
    (presentation 𝒜 ℳ).cohomologyZeroSectionMap ((d : ℤ) + n)
        (GradedMonoid.GSMul.smul (A := fun i : ℕ ↦ 𝒜 i)
          (M := fun j : ℤ ↦ (ℳ j : Type u)) a m) =
      GradedMonoid.GSMul.smul (A := fun i : ℕ ↦ 𝒜 i)
        (M := Cohomology.degree 𝒜 ℳ) a
        ((presentation 𝒜 ℳ).cohomologyZeroSectionMap n m) := by
  change (Cohomology.sectionsEquiv 𝒜 ℳ ((d : ℤ) + n)).symm
      (sectionMap 𝒜 ℳ ((d : ℤ) + n) _) =
    (Cohomology.sectionsEquiv 𝒜 ℳ ((d : ℤ) + n)).symm
      (smul 𝒜 ℳ a ((Cohomology.sectionsEquiv 𝒜 ℳ n)
        ((Cohomology.sectionsEquiv 𝒜 ℳ n).symm (sectionMap 𝒜 ℳ n m))))
  rw [AddEquiv.apply_symm_apply]
  congr 1
  apply Subtype.ext
  funext z
  apply Subtype.ext
  change LocalizedModule.mk ((a : A) • (m : M)) _ =
    LocalizedModule.map _ (LinearMap.lsmul A M (a : A)) (LocalizedModule.mk (m : M) _)
  rw [LocalizedModule.map_mk]
  rfl

/-- The additive truncated section map is `A`-linear when all discarded homogeneous pieces
vanish. -/
@[stacks 0B5R "linearity law for the truncated shifted-section map"]
theorem map_smul [DirectSum.Decomposition ℳ] (k : ℤ)
    (lowerPiecesVanish : ∀ n : ℤ, n < k → IsZero (AddCommGrpCat.of (ℳ n)))
    (a : A) (m : M) :
    mapAdd 𝒜 ℳ k (a • m) = a • mapAdd 𝒜 ℳ k m := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [_root_.add_smul, _root_.map_add, ha, hb]
  | homogeneous a =>
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | add m m' hm hm' => simp only [_root_.smul_add, _root_.map_add, hm, hm']
    | homogeneous m =>
      rename_i d n
      by_cases hn : k ≤ n
      · have hdn : k ≤ (d : ℤ) + n := le_trans hn (by omega)
        let am : ℳ ((d : ℤ) + n) :=
          GradedMonoid.GSMul.smul (A := fun i : ℕ ↦ 𝒜 i)
            (M := fun j : ℤ ↦ (ℳ j : Type u)) a m
        change mapAdd 𝒜 ℳ k (am : M) = _
        rw [mapAdd_of, dif_pos hdn, mapAdd_of, dif_pos hn,
          Cohomology.smul_of, ← cohomologyZeroSectionMap_smul]
        rfl
      · letI : Subsingleton (ℳ n) :=
          AddCommGrpCat.subsingleton_of_isZero (lowerPiecesVanish n (lt_of_not_ge hn))
        have hm : m = 0 := Subsingleton.elim _ _
        simp [hm]

/-- The canonical linear map from a graded module to lower-truncated cohomology of its shifted
associated sheaves. -/
@[stacks 0B5R "linear truncated section map for shifted associated sheaves"]
noncomputable def map [DirectSum.Decomposition ℳ] (k : ℤ)
    (lowerPiecesVanish : ∀ n : ℤ, n < k → IsZero (AddCommGrpCat.of (ℳ n))) :
    M →ₗ[A] Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k :=
  { mapAdd 𝒜 ℳ k with
    map_smul' := map_smul 𝒜 ℳ k lowerPiecesVanish }

/-- On a homogeneous element, the truncated linear map is the transported section map above the
truncation bound and is zero below it. -/
@[simp, stacks 0B5R "truncated shifted-section map on a homogeneous element"]
theorem map_of [DirectSum.Decomposition ℳ] (k : ℤ)
    (lowerPiecesVanish : ∀ n : ℤ, n < k → IsZero (AddCommGrpCat.of (ℳ n)))
    (n : ℤ) (m : ℳ n) :
    map 𝒜 ℳ k lowerPiecesVanish (m : M) =
      if h : k ≤ n then
        DirectSum.of
          (DirectSum.Gmodule.LowerBound.pieces k
            (Proj.AssociatedModule.ShiftedSections.Cohomology.degree 𝒜 ℳ)) ⟨n, h⟩
          ((Proj.AssociatedModule.ShiftedSections.presentation 𝒜 ℳ).cohomologyZeroSectionMap n m)
      else 0 :=
  mapAdd_of 𝒜 ℳ k n m

end Proj.AssociatedModule.ShiftedSections.Truncated

namespace Proj.AssociatedModule.ShiftComparison.CohomologyZero

/-- If the positive degrees of a finite homogeneous generating set divide `d`, then in every
degree divisible by `d` the induced map on degree-zero cohomology is an isomorphism. -/
theorem isIso_of_dvd_generatorDegrees
    (C : ShiftComparison 𝒜 ℳ) (d : ℕ) (generators : Finset A)
    (generatorDegree : {x // x ∈ generators} → ℕ)
    (hgenerated : Algebra.adjoin (𝒜 0) (generators : Set A) = ⊤)
    (hhomogeneous : ∀ x : {x // x ∈ generators}, x.1 ∈ 𝒜 (generatorDegree x))
    (hpositive : ∀ x : {x // x ∈ generators}, 0 < generatorDegree x)
    (hd_dvd : ∀ x : {x // x ∈ generators}, generatorDegree x ∣ d)
    (n : ℤ) (hn : (d : ℤ) ∣ n) :
    IsIso (RingedSpace.moduleCohomologyMap (C.hom n) 0) := by
  have h := ShiftComparison.hom_isIso_of_dvd_generatorDegrees 𝒜 ℳ C d generators
    generatorDegree hgenerated hhomogeneous hpositive hd_dvd n hn
  letI : @IsIso (SheafOfModules.{u} (Proj 𝒜).toRingedSpace.ringCatSheaf)
      _ _ _ (C.hom n) := h
  exact Functor.map_isIso
    ((SheafOfModules.toSheaf (Proj 𝒜).toRingedSpace.ringCatSheaf) ⋙
      Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology (Proj 𝒜)) 0 ⋙
      (evaluation _ _).obj (Opposite.op (⊤ : (Proj 𝒜).Opens))) (C.hom n)

/-- The degree-zero cohomology comparison is an isomorphism in every degree divisible by the
period of a chosen finite set of positive homogeneous generators. -/
@[stacks 0B5R "periodic degree-zero cohomology comparison"]
theorem isIso_of_period
    (C : ShiftComparison 𝒜 ℳ) (G : GradedAlgebra.PositiveGenerators 𝒜)
    (n : ℤ) (hn : (G.period : ℤ) ∣ n) :
    IsIso (RingedSpace.moduleCohomologyMap (C.hom n) 0) := by
  exact isIso_of_dvd_generatorDegrees 𝒜 ℳ C G.period G.elems G.degree
    G.generates G.homogeneous G.positive
    (fun x ↦ Finset.dvd_lcm (Finset.mem_attach _ x)) n hn

/-- For the canonical shift comparison, the degree-zero cohomology map is an isomorphism in
every degree divisible by the period of positive homogeneous generators. -/
@[stacks 0B5R "canonical periodic degree-zero cohomology comparison"]
theorem canonicalIsIso_of_period
    [DirectSum.Decomposition ℳ]
    (G : GradedAlgebra.PositiveGenerators 𝒜)
    (n : ℤ) (hn : (G.period : ℤ) ∣ n) :
    IsIso (RingedSpace.moduleCohomologyMap
      ((Proj.AssociatedModule.ShiftComparison.canonical 𝒜 ℳ).hom n) 0) :=
  isIso_of_period 𝒜 ℳ (Proj.AssociatedModule.ShiftComparison.canonical 𝒜 ℳ) G n hn

end Proj.AssociatedModule.ShiftComparison.CohomologyZero

namespace Proj.AssociatedModule.FiniteSections

/-- For a finite internally graded module over a Noetherian graded ring, every truncation of
canonically acted-on degree-zero cohomology of the tensor twists of its associated sheaf is a
finite module. -/
@[stacks 0B5R "finite truncated tensor-twist sections"]
theorem tensorTwist_finite
    [IsNoetherianRing A] [DirectSum.Decomposition ℳ] [Module.Finite A M]
    (k : ℤ) :
    Module.Finite A
      (Proj.TwistedSections.Cohomology.truncated 𝒜 (sheaf 𝒜 ℳ) k) := by
  let N : GradedModule.Left 𝒜 ℤ := { carrier := M, grading := ℳ }
  let Nfg : GradedModule.Left.FG 𝒜 ℤ := ⟨N, inferInstanceAs (Module.Finite A M)⟩
  have hgroup : GradedModule.Left.instAddCommGroup N = ‹AddCommGroup M› :=
    AddCommGroup.ext rfl
  have hs : Proj.Associated.obj 𝒜 N = sheaf 𝒜 ℳ := by
    dsimp only [Proj.Associated.obj]
    congr! (closePost := false) 1
  have hcoh := Proj.Associated.isCoherent 𝒜 Nfg
  change SheafOfModules.IsCoherent (Proj.Associated.obj 𝒜 N) at hcoh
  rw [hs] at hcoh
  letI : (sheaf 𝒜 ℳ).IsCoherent := hcoh
  exact Proj.Coherent.truncatedSections_finite 𝒜 _ k

/-- For a finite internally graded module over a Noetherian graded ring, every truncation of
canonically acted-on degree-zero cohomology of the sheaves associated to its shifted gradings is
a finite module. -/
@[stacks 0B5R "finite truncated shifted sections"]
theorem shifted_finite
    [IsNoetherianRing A] [DirectSum.Decomposition ℳ] [Module.Finite A M]
    (k : ℤ) :
    Module.Finite A
      (Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k) := sorry

/-- For a finite internally graded module over a Noetherian graded ring, the canonical map from
each homogeneous piece to degree-zero cohomology of its shifted associated sheaf is an
isomorphism in all sufficiently large degrees. -/
@[stacks 0B5R "eventual isomorphism for shifted section maps"]
theorem sectionMap_eventually_isIso
    [IsNoetherianRing A] [DirectSum.Decomposition ℳ] [Module.Finite A M] :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n →
      IsIso (AddCommGrpCat.ofHom
        ((ShiftedSections.presentation 𝒜 ℳ).cohomologyZeroSectionMap n)) := sorry

end Proj.AssociatedModule.FiniteSections

end AlgebraicGeometry
