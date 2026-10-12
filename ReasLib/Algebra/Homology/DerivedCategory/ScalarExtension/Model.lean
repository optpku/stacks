/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.BoundedAbove
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Monoidal
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective
public import ReasLib.CategoryTheory.Iso.Explicit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Models for derived extension of scalars

@stack 064M

K-flat complexes compute derived extension of scalars.  The bounded-above termwise-flat
criterion is exposed separately so downstream code can stay at the model properties it naturally
has, without rebuilding derived-functor instances.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.ModuleCat.DerivedExtension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The derived-extension comparison is invertible on a K-flat cochain model. -/
@[stacks 064M "K-flat model for derived extension of scalars"]
theorem counit_isIso_of_isKFlat
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlatOver) :
    IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app K) := sorry

/-- The cochain-level derived-extension counit as an isomorphism, from an explicit invertibility
certificate.  Keeping the certificate explicit avoids installing a proof-local `IsIso` instance
when a downstream comparison needs the inverse. -/
@[stacks 064M "derived-extension counit isomorphism"]
noncomputable def counitIso
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (h : IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app K)) :
    (ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CategoryTheory.IsIso.toIso h

/-- The forward map of `counitIso` is the canonical derived-extension counit component. -/
@[simp, stacks 064M "derived-extension counit isomorphism forward map"]
theorem counitIso_hom
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (h : IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app K)) :
    (counitIso σ K h).hom = (ModuleCat.derivedExtensionComplexCounit σ).app K := rfl

/-- The derived-extension counit isomorphism is independent of the supplied invertibility proof. -/
@[stacks 064M "derived-extension counit isomorphism proof independence"]
theorem counitIso_eq
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (h₁ h₂ : IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app K)) :
    counitIso σ K h₁ = counitIso σ K h₂ := by
  rfl

/-- The derived-extension counit as a concrete isomorphism on a K-flat cochain model. -/
@[stacks 064M "K-flat derived-extension counit isomorphism"]
noncomputable def counitIso_of_isKFlat
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlatOver) :
    (ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  counitIso σ K (counit_isIso_of_isKFlat σ K hK)

/-- The forward map of the K-flat counit isomorphism is the canonical derived-extension
counit component. -/
@[simp, stacks 064M "K-flat derived-extension counit forward map"]
theorem counitIso_of_isKFlat_hom
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlatOver) :
    (counitIso_of_isKFlat σ K hK).hom =
      (ModuleCat.derivedExtensionComplexCounit σ).app K := rfl

namespace BoundedAbove

/-- A bounded-above termwise-flat cochain complex computes derived extension of scalars. -/
@[stacks 064M "bounded-above flat model for derived extension of scalars"]
theorem counit_isIso_of_isTermwiseFlat
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hKflat : HomologicalComplex.IsTermwiseFlat K) :
    IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app K) :=
  counit_isIso_of_isKFlat σ K
    ((CochainComplex.isKFlatOver_iff_isKFlat K).2
      (CochainComplex.isKFlat_of_boundedAbove_of_flat K hK hKflat))

/-- A bounded-above termwise finite-projective complex computes derived extension of scalars. -/
@[stacks 064M "bounded-above finite-projective model for derived extension of scalars"]
theorem counit_isIso_of_isTermwiseFiniteProjective
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hKfp : K.IsTermwiseFiniteProjective) :
    IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app K) :=
  counit_isIso_of_isTermwiseFlat σ K hK hKfp.termwiseFlat

/-- The derived-extension counit as a concrete isomorphism on a bounded-above termwise-flat
cochain model. -/
@[stacks 064M "bounded-above flat derived-extension counit isomorphism"]
noncomputable def counitIso_of_isTermwiseFlat
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hKflat : HomologicalComplex.IsTermwiseFlat K) :
    (ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  counitIso σ K (counit_isIso_of_isTermwiseFlat σ K hK hKflat)

/-- The forward map of the bounded-above flat counit isomorphism is the canonical
derived-extension counit component. -/
@[simp, stacks 064M "bounded-above flat derived-extension counit forward map"]
theorem counitIso_of_isTermwiseFlat_hom
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hKflat : HomologicalComplex.IsTermwiseFlat K) :
    (counitIso_of_isTermwiseFlat σ K hK hKflat).hom =
      (ModuleCat.derivedExtensionComplexCounit σ).app K := rfl

/-- The derived-extension counit as a concrete isomorphism on a bounded-above termwise
finite-projective cochain model. -/
@[stacks 064M "bounded-above finite-projective derived-extension counit isomorphism"]
noncomputable def counitIso_of_isTermwiseFiniteProjective
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hKfp : K.IsTermwiseFiniteProjective) :
    (ModuleCat.derivedExtensionOfScalars σ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  counitIso σ K
    (counit_isIso_of_isTermwiseFiniteProjective σ K hK hKfp)

/-- The forward map of the bounded-above finite-projective counit isomorphism is the canonical
derived-extension counit component. -/
@[simp, stacks 064M "bounded-above finite-projective derived-extension counit forward map"]
theorem counitIso_of_isTermwiseFiniteProjective_hom
    (σ : R →+* S) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hKfp : K.IsTermwiseFiniteProjective) :
    (counitIso_of_isTermwiseFiniteProjective σ K hK hKfp).hom =
      (ModuleCat.derivedExtensionComplexCounit σ).app K := rfl

end BoundedAbove

end CategoryTheory.ModuleCat.DerivedExtension
