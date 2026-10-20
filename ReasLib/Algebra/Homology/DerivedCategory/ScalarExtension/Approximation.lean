module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cardinally bounded derived base-change approximations

@stack 0GYI

This leaf owns the concrete comparison and homology maps used by the cardinal approximation
lemma for a map of complexes.  The chapter-facing theorem is a thin specialization of the
source-independent `Approximation` proposition below.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- The cardinal of all terms of a cochain complex, with the degree remembered. -/
@[stacks 0GYI "total cardinal of a cochain complex"]
def totalCardinal (K : CochainComplex (ModuleCat.{v, u} R) ℤ) : Cardinal.{max u v + 1} :=
  Cardinal.lift.{max u v + 1, max u v}
    (Cardinal.mk (ULift.{max u v} (Σ i : ℤ, (K.X i : Type v))))

end CochainComplex

namespace ModuleCat.DerivedExtension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Stacks 0GYI: cochain complexes of modules over a ring. -/
@[stacks 0GYI "cochain complexes of modules"]
abbrev Cpx (R : Type u) [Ring R] := CochainComplex (ModuleCat.{u, u} R) ℤ

/-- The cochain-level restriction-of-scalars functor for a ring homomorphism. -/
@[stacks 0GYI "cochain restriction of scalars"]
abbrev restrictionComplex (σ : R →+* S) : Cpx S ⥤ Cpx R :=
  (ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex (up ℤ)

/-- The derived base-change comparison attached to a map of cochain complexes. -/
@[stacks 0GYI "derived base-change comparison"]
noncomputable def comparison {M : Cpx R} {N : Cpx S}
    (σ : R →+* S) (a : M ⟶ (restrictionComplex σ).obj N) :
    (ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj N :=
  (ModuleCat.derivedExtensionRestrictionHomEquiv σ _ _).symm
    (DerivedCategory.Q.map a ≫ (ModuleCat.derivedRestrictionComplexUnit σ).app N)

/-- The map of restricted complexes induced by a compatible pair of subobjects. -/
@[stacks 0GYI "restriction to compatible subcomplexes"]
noncomputable def restrict {M : Cpx R} {N : Cpx S}
    (σ : R →+* S) (M₁ : Subobject M) (N₁ : Subobject N)
    (a : M ⟶ (restrictionComplex σ).obj N)
    (h : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors
      (M₁.arrow ≫ a)) :
    (M₁ : Cpx R) ⟶ (restrictionComplex σ).obj (N₁ : Cpx S) :=
  (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).factorThru
      (M₁.arrow ≫ a) h ≫
    (Subobject.underlyingIso ((restrictionComplex σ).map N₁.arrow)).hom

/-- The induced degree-`i` homology map for a compatible pair of subcomplexes. -/
@[stacks 0GYI "homology map of a compatible base-change pair"]
noncomputable def homologyMap {M : Cpx R} {N : Cpx S}
    (σ : R →+* S) (M₁ : Subobject M) (N₁ : Subobject N)
    (a : M ⟶ (restrictionComplex σ).obj N)
    (hf : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors
      (M₁.arrow ≫ a)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).obj
        ((ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj (M₁ : Cpx R))) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).obj
        (DerivedCategory.Q.obj (N₁ : Cpx S)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).map
    (comparison σ (restrict σ M₁ N₁ a hf))

/-- The homology map induced by enlarging the source subcomplex. -/
@[stacks 0GYI "homology map of a source enlargement"]
noncomputable def sourceMap {M : Cpx R}
    (σ : R →+* S) (M₁ M₂ : Subobject M) (hM : M₁ ≤ M₂) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).obj
        ((ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj (M₁ : Cpx R))) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).obj
        ((ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj (M₂ : Cpx R))) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).map
    ((ModuleCat.derivedExtensionOfScalars σ).map
      (DerivedCategory.Q.map (Subobject.ofLE M₁ M₂ hM)))

/-- The homology map induced by enlarging the target subcomplex. -/
@[stacks 0GYI "homology map of a target enlargement"]
noncomputable def targetMap {N : Cpx S}
    (N₁ N₂ : Subobject N) (hN : N₁ ≤ N₂) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).obj
        (DerivedCategory.Q.obj (N₁ : Cpx S)) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).obj
        (DerivedCategory.Q.obj (N₂ : Cpx S)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u, u} S) i).map
    (DerivedCategory.Q.map (Subobject.ofLE N₁ N₂ hN))

/-- The cardinal of the disjoint union of all source and target terms.  This is the formal
counterpart of the source expression `|⋃ Mⁱ ∪ ⋃ Nⁱ|`; the degree index is retained in each sigma. -/
@[stacks 0GYI "pair cardinal of two complexes"]
def pairCardinal {M : Cpx R} {N : Cpx S} : Cardinal :=
  M.totalCardinal + N.totalCardinal

/-- A compatible enlargement of a pair of source and target subcomplexes.  The subobjects are
concrete fields; only the containment and compatibility laws are propositions. -/
@[stacks 0GYI "compatible subcomplex enlargement"]
structure Enlargement {M : Cpx R} {N : Cpx S} (σ : R →+* S)
    (a : M ⟶ (restrictionComplex σ).obj N) (M₁ : Subobject M) (N₁ : Subobject N)
    (h₁ : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors (M₁.arrow ≫ a)) where
  /-- The enlarged source subcomplex. -/
  source : Subobject M
  /-- The enlarged target subcomplex. -/
  target : Subobject N
  /-- The source enlargement contains the initial source subcomplex. -/
  source_le : M₁ ≤ source
  /-- The target enlargement contains the initial target subcomplex. -/
  target_le : N₁ ≤ target
  /-- The original map restricts to the enlarged pair. -/
  compatible :
    (Subobject.mk ((restrictionComplex σ).map target.arrow)).Factors (source.arrow ≫ a)

/-- The kernel-control clause for an enlargement. -/
@[stacks 0GYI "kernel control for a subcomplex enlargement"]
def KernelControl {M : Cpx R} {N : Cpx S} {σ : R →+* S}
    {a : M ⟶ (restrictionComplex σ).obj N} {M₁ : Subobject M} {N₁ : Subobject N}
    {h₁ : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors (M₁.arrow ≫ a)}
    (E : Enlargement σ a M₁ N₁ h₁) : Prop :=
  ∀ i : ℤ,
    (kernelSubobject (homologyMap σ M₁ N₁ a h₁ i)).arrow ≫
      sourceMap σ M₁ E.source E.source_le i = 0

/-- The image-control clause for an enlargement. -/
@[stacks 0GYI "image control for a subcomplex enlargement"]
def ImageControl {M : Cpx R} {N : Cpx S} {σ : R →+* S}
    {a : M ⟶ (restrictionComplex σ).obj N} {M₁ : Subobject M} {N₁ : Subobject N}
    {h₁ : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors (M₁.arrow ≫ a)}
    (E : Enlargement σ a M₁ N₁ h₁) : Prop :=
  ∀ i : ℤ,
    imageSubobject (targetMap N₁ E.target E.target_le i) ≤
      imageSubobject (homologyMap σ E.source E.target a E.compatible i)

/-- The cardinal bound for an enlargement. -/
@[stacks 0GYI "cardinal bound for a subcomplex enlargement"]
def CardinalBound {M : Cpx R} {N : Cpx S} {σ : R →+* S}
    {a : M ⟶ (restrictionComplex σ).obj N} {M₁ : Subobject M} {N₁ : Subobject N}
    {h₁ : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors (M₁.arrow ≫ a)}
    (κ : Cardinal) (E : Enlargement σ a M₁ N₁ h₁) : Prop :=
  pairCardinal (M := (E.source : Cpx R)) (N := (E.target : Cpx S)) ≤
    max κ (pairCardinal (M := (M₁ : Cpx R)) (N := (N₁ : Cpx S)))

/-- The three independent source clauses packaged over explicit enlargement data. -/
@[stacks 0GYI "controls for a subcomplex enlargement"]
structure Controls {M : Cpx R} {N : Cpx S} {σ : R →+* S}
    {a : M ⟶ (restrictionComplex σ).obj N} {M₁ : Subobject M} {N₁ : Subobject N}
    {h₁ : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors (M₁.arrow ≫ a)}
    (κ : Cardinal) (E : Enlargement σ a M₁ N₁ h₁) : Prop where
  /-- Kernel classes from the initial pair vanish after mapping to the enlargement. -/
  kernel : KernelControl E
  /-- Initial target homology classes lie in the image from the enlarged source. -/
  image : ImageControl E
  /-- The enlargement has the prescribed cardinal bound. -/
  cardinal : CardinalBound κ E

/-- The canonical cardinal attached to a commutative-ring map. -/
@[stacks 0GYI "cardinal attached to a ring map"]
def mapCardinal (_ : R →+* S) : Cardinal.{u + 1} :=
  max (Cardinal.lift.{u + 1, u} (Cardinal.mk R))
    (max (Cardinal.lift.{u + 1, u} (Cardinal.mk S))
      (Cardinal.lift.{u + 1, u} Cardinal.aleph0))

/-- The approximation property at a specified cardinal bound. -/
@[stacks 0GYI "cardinally bounded derived base-change approximation at a bound"]
def ApproximationAt (σ : R →+* S) (κ : Cardinal.{u + 1}) : Prop :=
  ∀ {M : Cpx R} {N : Cpx S}
      (a : M ⟶ (restrictionComplex σ).obj N)
      [IsIso (comparison σ a)]
      (M₁ : Subobject M) (N₁ : Subobject N)
      (h₁ : (Subobject.mk ((restrictionComplex σ).map N₁.arrow)).Factors
        (M₁.arrow ≫ a)),
      ∃ E : Enlargement σ a M₁ N₁ h₁, Controls κ E

/-- The source-facing cardinal approximation property for a derived base-change map. -/
@[stacks 0GYI "cardinally bounded derived base-change approximation"]
def Approximation (σ : R →+* S) : Prop :=
  ∃ κ : Cardinal.{u + 1}, ApproximationAt σ κ

/-- Canonical-bound companion for the cardinal approximation theorem. -/
@[stacks 0GYI "derived base-change approximation at the canonical bound"]
theorem approximation_at (σ : R →+* S) : ApproximationAt σ (mapCardinal σ) := sorry

/-- Lemma 15.103.5 (0GYI): every commutative-ring map has a cardinally bounded derived
base-change approximation. -/
@[stacks 0GYI "derived base-change approximation theorem"]
theorem approximation (σ : R →+* S) : Approximation σ := sorry

end ModuleCat.DerivedExtension

end CategoryTheory
