/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Left

@[expose] public section

/-!
# K-Projective Resolutions

This leaf specializes Mathlib's left-resolution category to the object property of being
K-projective and the morphism property of being a quasi-isomorphism.  It introduces only the
reusable resolution data and its computation and naturality API; existence hypotheses belong
in separate application-specific leaves.
-/

open CategoryTheory CategoryTheory.ObjectProperty

universe u v

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object property of K-projective cochain complexes. -/
@[stacks 064B "K-projective cochain complexes"]
def kProjective (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (CochainComplex A ℤ) :=
  fun P => P.IsKProjective

/-- Membership in `kProjective A` is the usual K-projectivity predicate. -/
@[simp]
theorem mem_kProjective_iff (P : CochainComplex A ℤ) :
    kProjective A P ↔ P.IsKProjective := sorry

/-- A K-projective resolution of `K` is Mathlib's left resolution of `K` by a K-projective
complex along a quasi-isomorphism. -/
@[stacks 064B "K-projective left resolution"]
abbrev KProjectiveResolution (K : CochainComplex A ℤ) :=
  ObjectProperty.LeftResolution (kProjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

namespace KProjectiveResolution

/-- Construct a K-projective resolution from an explicit complex and comparison. -/
def mk {K : CochainComplex A ℤ} (P : CochainComplex A ℤ) (hP : P.IsKProjective)
    (f : P ⟶ K) (hf : QuasiIso f) : KProjectiveResolution K :=
  ObjectProperty.LeftResolution.mk ⟨P, hP⟩ f hf

/-- The bundled K-projective model underlying a resolution. -/
abbrev model {K : CochainComplex A ℤ} (R : KProjectiveResolution K) :
    (kProjective A).FullSubcategory :=
  R.X₁

/-- The K-projective resolving complex. -/
abbrev complex {K : CochainComplex A ℤ} (R : KProjectiveResolution K) :
    CochainComplex A ℤ :=
  R.model.obj

/-- The resolving complex is K-projective. -/
theorem isKProjective {K : CochainComplex A ℤ} (R : KProjectiveResolution K) :
    R.complex.IsKProjective := sorry

/-- The comparison map from the K-projective model to the original complex. -/
abbrev π {K : CochainComplex A ℤ} (R : KProjectiveResolution K) : R.complex ⟶ K :=
  R.w

/-- The comparison map is a quasi-isomorphism. -/
theorem quasiIso {K : CochainComplex A ℤ} (R : KProjectiveResolution K) :
    QuasiIso R.π := sorry

attribute [instance] isKProjective quasiIso

/-- A bundled K-projective resolution coerces to its resolving cochain complex. -/
instance {K : CochainComplex A ℤ} :
    CoeOut (KProjectiveResolution K) (CochainComplex A ℤ) where
  coe P := P.complex

/-- The morphism of resolving complexes underlying a morphism of K-projective resolutions. -/
abbrev hom {K : CochainComplex A ℤ} {R S : KProjectiveResolution K} (f : R ⟶ S) :
    R.complex ⟶ S.complex :=
  ObjectProperty.LeftResolution.hom f

/-- A morphism of K-projective resolutions commutes with the comparison maps. -/
@[reassoc]
theorem π_naturality {K : CochainComplex A ℤ} {R S : KProjectiveResolution K} (f : R ⟶ S) :
    hom f ≫ S.π = R.π := sorry

/-- The functor selecting the bundled K-projective model of a resolution. -/
abbrev modelFunctor (K : CochainComplex A ℤ) :
    KProjectiveResolution K ⥤ (kProjective A).FullSubcategory :=
  ObjectProperty.LeftResolution.modelFunctor (kProjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

/-- The functor selecting the resolving complex of a K-projective resolution. -/
abbrev complexFunctor (K : CochainComplex A ℤ) :
    KProjectiveResolution K ⥤ CochainComplex A ℤ :=
  ObjectProperty.LeftResolution.objectFunctor (kProjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

/-- The comparison maps from K-projective models form a natural transformation. -/
abbrev πNatTrans (K : CochainComplex A ℤ) :
    complexFunctor K ⟶ (Functor.const (KProjectiveResolution K)).obj K :=
  ObjectProperty.LeftResolution.comparisonNatTrans (kProjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

/-- The named constructor retains the supplied resolving complex. -/
@[simp]
theorem mk_complex {K : CochainComplex A ℤ} (P : CochainComplex A ℤ)
    (hP : P.IsKProjective) (f : P ⟶ K) (hf : QuasiIso f) :
    (mk P hP f hf).complex = P := sorry

/-- The named constructor retains the supplied comparison. -/
@[simp]
theorem mk_π {K : CochainComplex A ℤ} (P : CochainComplex A ℤ)
    (hP : P.IsKProjective) (f : P ⟶ K) (hf : QuasiIso f) :
    (mk P hP f hf).π = f := sorry

/-- K-projective resolutions exist exactly when explicit K-projective comparison data exist. -/
theorem nonempty_iff {K : CochainComplex A ℤ} :
    Nonempty (KProjectiveResolution K) ↔
      ∃ (P : CochainComplex A ℤ) (_ : P.IsKProjective) (f : P ⟶ K), QuasiIso f := sorry

end KProjectiveResolution

end CochainComplex
