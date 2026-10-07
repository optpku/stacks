module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right

@[expose] public section

/-!
# K-Injective Resolutions

This leaf specializes Mathlib's right-resolution category to the object property of being
K-injective and the morphism property of being a quasi-isomorphism.  It is independent of any
construction or existence theorem, so derived-category consumers can state resolution
hypotheses without importing a particular replacement method.
-/

open CategoryTheory CategoryTheory.ObjectProperty

universe u v

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object property of K-injective cochain complexes. -/
@[stacks 090Y "K-injective cochain complexes"]
def kInjective (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (CochainComplex A ℤ) :=
  fun I => I.IsKInjective

/-- Membership in `kInjective A` is the usual K-injectivity predicate. -/
@[simp]
theorem mem_kInjective_iff (I : CochainComplex A ℤ) :
    kInjective A I ↔ I.IsKInjective := sorry

/-- A K-injective resolution of `K` is Mathlib's right resolution of `K` by a K-injective
complex along a quasi-isomorphism. -/
@[stacks 090Y "K-injective right resolution"]
abbrev KInjectiveResolution (K : CochainComplex A ℤ) :=
  ObjectProperty.RightResolution (kInjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

namespace KInjectiveResolution

/-- Construct a K-injective resolution from an explicit complex and comparison. -/
def mk {K : CochainComplex A ℤ} (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (f : K ⟶ I) (hf : QuasiIso f) : KInjectiveResolution K :=
  ObjectProperty.RightResolution.mk ⟨I, hI⟩ f hf

/-- The bundled K-injective model underlying a resolution. -/
abbrev model {K : CochainComplex A ℤ} (R : KInjectiveResolution K) :
    (kInjective A).FullSubcategory :=
  R.X₁

/-- The K-injective resolving complex. -/
abbrev complex {K : CochainComplex A ℤ} (R : KInjectiveResolution K) :
    CochainComplex A ℤ :=
  R.model.obj

/-- The resolving complex is K-injective. -/
theorem isKInjective {K : CochainComplex A ℤ} (R : KInjectiveResolution K) :
    R.complex.IsKInjective := sorry

/-- The comparison map from the original complex to the K-injective model. -/
abbrev ι {K : CochainComplex A ℤ} (R : KInjectiveResolution K) : K ⟶ R.complex :=
  R.w

/-- The comparison map is a quasi-isomorphism. -/
theorem quasiIso {K : CochainComplex A ℤ} (R : KInjectiveResolution K) :
    QuasiIso R.ι := sorry

attribute [instance] isKInjective quasiIso

/-- A bundled K-injective resolution coerces to its resolving cochain complex. -/
instance {K : CochainComplex A ℤ} :
    CoeOut (KInjectiveResolution K) (CochainComplex A ℤ) where
  coe I := I.complex

/-- The morphism of resolving complexes underlying a morphism of K-injective resolutions. -/
abbrev hom {K : CochainComplex A ℤ} {R S : KInjectiveResolution K} (f : R ⟶ S) :
    R.complex ⟶ S.complex :=
  ObjectProperty.RightResolution.hom f

/-- A morphism of K-injective resolutions commutes with the comparison maps. -/
@[reassoc]
theorem ι_naturality {K : CochainComplex A ℤ} {R S : KInjectiveResolution K} (f : R ⟶ S) :
    R.ι ≫ hom f = S.ι := sorry

/-- The functor selecting the bundled K-injective model of a resolution. -/
abbrev modelFunctor (K : CochainComplex A ℤ) :
    KInjectiveResolution K ⥤ (kInjective A).FullSubcategory :=
  ObjectProperty.RightResolution.modelFunctor (kInjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

/-- The functor selecting the resolving complex of a K-injective resolution. -/
abbrev complexFunctor (K : CochainComplex A ℤ) :
    KInjectiveResolution K ⥤ CochainComplex A ℤ :=
  ObjectProperty.RightResolution.objectFunctor (kInjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

/-- The comparison maps into K-injective models form a natural transformation. -/
abbrev ιNatTrans (K : CochainComplex A ℤ) :
    (Functor.const (KInjectiveResolution K)).obj K ⟶ complexFunctor K :=
  ObjectProperty.RightResolution.comparisonNatTrans (kInjective A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

/-- The named constructor retains the supplied resolving complex. -/
@[simp]
theorem mk_complex {K : CochainComplex A ℤ} (I : CochainComplex A ℤ)
    (hI : I.IsKInjective) (f : K ⟶ I) (hf : QuasiIso f) :
    (mk I hI f hf).complex = I := sorry

/-- The named constructor retains the supplied comparison. -/
@[simp]
theorem mk_ι {K : CochainComplex A ℤ} (I : CochainComplex A ℤ)
    (hI : I.IsKInjective) (f : K ⟶ I) (hf : QuasiIso f) :
    (mk I hI f hf).ι = f := sorry

/-- K-injective resolutions exist exactly when explicit K-injective comparison data exist. -/
theorem nonempty_iff {K : CochainComplex A ℤ} :
    Nonempty (KInjectiveResolution K) ↔
      ∃ (I : CochainComplex A ℤ) (_ : I.IsKInjective) (f : K ⟶ I), QuasiIso f := sorry

end KInjectiveResolution

end CochainComplex
