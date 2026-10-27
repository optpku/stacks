/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.OrderedCech
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion

/-!
# Closed support from the explicit finite ordered Cech complex

Tensor totalization with `OrderedCech.complex f` is specified before localization. Its descent
uses only the localization universal property of the existing derived category. In particular,
this construction does not invoke a general derived-tensor existence certificate.

The forward map to the identity is specified before localization: tensor the ordered Cech
projection to the regular single complex with the input, then apply the tensor left unitor.
The resulting natural transformation descends through the same localization universal property.

The quasi-isomorphism, torsion-cohomology, and adjunction assertions below remain proof debt.
No object, map, or comparison is selected from the adjunction assertion.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology.ClosedSupportModel

variable {A : Type u} [CommRing A]

/-- Actual tensor totalization with the integer-indexed extended ordered Cech complex.
In degree `n` it is the coproduct of `Cech(f)^p ⊗ K^q` over `p + q = n`; its map on a chain
map `g` is induced by the identity on the Cech factor and the components of `g`. -/
abbrev complexFunctor {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj (OrderedCech.complex f)

/-- The degree-zero Cech term is the regular module, using the actual extension comparison.
The nonnegative extended complex has this term definitionally, by `CochainComplex.augment`. -/
def cechDegreeZeroIso {r : ℕ} (f : Fin r → A) :
    (OrderedCech.complex f).X 0 ≅ ModuleCat.of A A :=
  (LocalizedModule.Away.Cech.Ordered.extended f (ModuleCat.of A A)).extendXIso
    ComplexShape.embeddingUpNat (i := (0 : ℕ)) rfl

/-- The genuine ordered Cech projection, with target expressed as the cochain tensor unit.
Its construction extends the nonnegative projection with degree-zero component the identity. -/
def cechProjection {r : ℕ} (f : Fin r → A) :
    OrderedCech.complex f ⟶ HomologicalComplex.tensorUnit (ModuleCat.{u} A) (up ℤ) :=
  OrderedCech.projection f

set_option backward.isDefEq.respectTransparency false in
/-- After identifying both degree-zero terms with `A`, the projection is the identity. -/
theorem cechProjection_f_zero {r : ℕ} (f : Fin r → A) :
    (cechProjection f).f 0 = (cechDegreeZeroIso f).hom ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 (ModuleCat.of A A)).inv := by
  dsimp only [cechProjection, OrderedCech.projection]
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
      (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl,
    HomologicalComplex.extendSingleIso_hom_f]
  simp [cechDegreeZeroIso, Category.assoc, Category.id_comp, Category.comp_id]
  exact Category.id_comp _

/-- Every component of the projection outside degree zero is zero. -/
theorem cechProjection_f_ne_zero {r : ℕ} (f : Fin r → A) (n : ℤ) (hn : n ≠ 0) :
    (cechProjection f).f n = 0 := by
  exact (HomologicalComplex.isZero_single_obj_X (up ℤ) 0
    (ModuleCat.of A A) n hn).eq_of_tgt _ _

/-- The projection kills the incoming differential in every degree. This includes the
degree-zero equation: the extension has zero source in degree `-1`. -/
theorem cechProjection_d {r : ℕ} (f : Fin r → A) (i j : ℤ) :
    (OrderedCech.complex f).d i j ≫ (cechProjection f).f j = 0 := by
  rw [← (cechProjection f).comm i j]
  simp only [HomologicalComplex.tensorUnit, HomologicalComplex.single_obj_d,
    CategoryTheory.Limits.comp_zero]

/-- Tensor the specified Cech projection with the identity of the variable complex. -/
def complexProjection {r : ℕ} (f : Fin r → A) :
    complexFunctor f ⟶ ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj
      (HomologicalComplex.tensorUnit (ModuleCat.{u} A) (up ℤ)) :=
  ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).map (cechProjection f)

theorem complexProjection_app {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (complexProjection f).app K =
      HomologicalComplex.mapBifunctorMap (cechProjection f) (𝟙 K)
        (curriedTensor (ModuleCat.{u} A)) (up ℤ) := rfl

/-- The existing cochain tensor-unit comparison. Its degree-zero summand uses the actual
module tensor unitor `A ⊗ Kⁿ → Kⁿ`, `a ⊗ x ↦ a • x`. -/
def tensorUnitComplexIso :
    ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj
      (HomologicalComplex.tensorUnit (ModuleCat.{u} A) (up ℤ)) ≅
        𝟭 (CochainComplex (ModuleCat.{u} A) ℤ) :=
  leftUnitorNatIso (CochainComplex (ModuleCat.{u} A) ℤ)

/-- The actual tensor projection to the input complex, before localization.
Totalization uses `d_C ⊗ 1 + p.negOnePow • (1 ⊗ d_K)` on bidegree `(p,q)`.
Only `p = 0` survives the projection, where the vertical sign is `1`. -/
def complexCounit {r : ℕ} (f : Fin r → A) :
    complexFunctor f ⟶ 𝟭 (CochainComplex (ModuleCat.{u} A) ℤ) :=
  complexProjection f ≫ tensorUnitComplexIso.hom

theorem complexCounit_app {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (complexCounit f).app K =
      HomologicalComplex.mapBifunctorMap (cechProjection f) (𝟙 K)
        (curriedTensor (ModuleCat.{u} A)) (up ℤ) ≫
          (HomologicalComplex.leftUnitor K).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- On every summand with nonzero Cech degree, the forward tensor map is zero. -/
theorem complexCounit_ι_of_ne_zero {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ) (h : p + q = n)
    (hp : p ≠ 0) :
    HomologicalComplex.ιMapBifunctor (OrderedCech.complex f) K
        (curriedTensor (ModuleCat.{u} A)) (up ℤ) p q n h ≫
      ((complexCounit f).app K).f n = 0 := by
  rw [complexCounit_app, HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap, cechProjection_f_ne_zero f p hp]
  simp [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero,
    Category.assoc, Category.id_comp, Category.comp_id]

/-- The cochain differential equation for the actual forward map. -/
theorem complexCounit_comm {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i j : ℤ) :
    ((complexFunctor f).obj K).d i j ≫ ((complexCounit f).app K).f j =
      ((complexCounit f).app K).f i ≫ K.d i j :=
  (((complexCounit f).app K).comm i j).symm

theorem complexCounit_naturality {r : ℕ} (f : Fin r → A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ L) :
    (complexFunctor f).map g ≫ (complexCounit f).app L =
      (complexCounit f).app K ≫ g :=
  (complexCounit f).naturality g

/-- Proof debt: the extended ordered Cech complex is supported in degrees `0, …, r`,
with finite products of flat principal localizations as its positive-degree terms. Bounded
flatness makes it K-flat, so the displayed tensor totalization preserves quasi-isomorphisms. -/
theorem complexFunctor_map_quasiIso {r : ℕ} (f : Fin r → A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ L) (hg : QuasiIso g) :
    QuasiIso ((complexFunctor f).map g) := sorry

/-- The specified tensor complex followed by the existing localization functor. -/
def cochainFunctor {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  complexFunctor f ⋙ (DerivedCategory.Q (C := ModuleCat.{u} A))

/-- The specified cochain functor inverts quasi-isomorphisms. The only additional input here
is the preceding preservation proposition; inverses are supplied by the existing localization. -/
theorem cochainFunctor_inverts {r : ℕ} (f : Fin r → A) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ)).IsInvertedBy
      (cochainFunctor f) := by
  intro K L g hg
  exact Localization.inverts (DerivedCategory.Q (C := ModuleCat.{u} A))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ))
    ((complexFunctor f).map g) (complexFunctor_map_quasiIso f g hg)

/-- Descend the actual fixed-Cech tensor functor to the existing derived-category model. -/
def ambient {r : ℕ} (f : Fin r → A) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Localization.lift (cochainFunctor f) (cochainFunctor_inverts f)
    (DerivedCategory.Q (C := ModuleCat.{u} A))

/-- The localization comparison, with both morphisms supplied by `Localization.fac`. -/
def ambientCompQIso {r : ℕ} (f : Fin r → A) :
    (DerivedCategory.Q (C := ModuleCat.{u} A)) ⋙ ambient f ≅ cochainFunctor f :=
  Localization.fac (cochainFunctor f) (cochainFunctor_inverts f)
    (DerivedCategory.Q (C := ModuleCat.{u} A))

/-- On a specified complex representative, the ambient functor computes its actual Cech tensor
complex. This is a comparison isomorphism, rather than a definitional equality of derived objects. -/
def representativeIso {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ambient f).obj ((DerivedCategory.Q (C := ModuleCat.{u} A)).obj K) ≅
      (DerivedCategory.Q (C := ModuleCat.{u} A)).obj ((complexFunctor f).obj K) :=
  (ambientCompQIso f).app K

/-- Apply the quotient functor to the already specified cochain forward map. -/
def cochainCounit {r : ℕ} (f : Fin r → A) :
    cochainFunctor f ⟶ DerivedCategory.Q (C := ModuleCat.{u} A) :=
  CategoryTheory.Functor.whiskerRight (complexCounit f)
      (DerivedCategory.Q (C := ModuleCat.{u} A)) ≫
    (Functor.leftUnitor (DerivedCategory.Q (C := ModuleCat.{u} A))).hom

@[simp]
theorem cochainCounit_app {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (cochainCounit f).app K =
      (DerivedCategory.Q (C := ModuleCat.{u} A)).map ((complexCounit f).app K) := by
  change (DerivedCategory.Q (C := ModuleCat.{u} A)).map ((complexCounit f).app K) ≫
      𝟙 _ = (DerivedCategory.Q (C := ModuleCat.{u} A)).map ((complexCounit f).app K)
  exact Category.comp_id _

/-- Descend the specified forward natural transformation through the genuine localization.
The two lifting comparisons are the existing `fac` comparison and the functor right unitor.
Neither the support proof nor the adjunction-existence proposition selects these DATA. -/
def ambientCounit {r : ℕ} (f : Fin r → A) :
    ambient f ⟶ 𝟭 (DerivedCategory (ModuleCat.{u} A)) := by
  letI : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{u} A))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ))
      (cochainFunctor f) (ambient f) := ⟨ambientCompQIso f⟩
  letI : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{u} A))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ))
      (DerivedCategory.Q (C := ModuleCat.{u} A))
      (𝟭 (DerivedCategory (ModuleCat.{u} A))) :=
    ⟨Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{u} A))⟩
  exact Localization.liftNatTrans (DerivedCategory.Q (C := ModuleCat.{u} A))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ))
    (cochainFunctor f) (DerivedCategory.Q (C := ModuleCat.{u} A))
    (ambient f) (𝟭 (DerivedCategory (ModuleCat.{u} A))) (cochainCounit f)

set_option backward.isDefEq.respectTransparency false in
/-- The descended forward map computes on every specified complex representative. -/
@[simp]
theorem ambientCounit_app_Q {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ambientCounit f).app ((DerivedCategory.Q (C := ModuleCat.{u} A)).obj K) =
      (representativeIso f K).hom ≫
        (DerivedCategory.Q (C := ModuleCat.{u} A)).map ((complexCounit f).app K) := by
  simp [ambientCounit, Localization.liftNatTrans_app, representativeIso, Category.comp_id]

/-- The quotient comparison as an equality of natural transformations. -/
theorem ambientCounit_whiskerQ {r : ℕ} (f : Fin r → A) :
    CategoryTheory.Functor.whiskerLeft (DerivedCategory.Q (C := ModuleCat.{u} A))
        (ambientCounit f) =
      (ambientCompQIso f).hom ≫ cochainCounit f ≫
        (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{u} A))).inv := by
  ext K
  change (ambientCounit f).app ((DerivedCategory.Q (C := ModuleCat.{u} A)).obj K) =
    (ambientCompQIso f).hom.app K ≫ (cochainCounit f).app K ≫ 𝟙 _
  rw [ambientCounit_app_Q, cochainCounit_app, Category.comp_id]
  rfl

theorem ambientCounit_naturality {r : ℕ} (f : Fin r → A)
    {K L : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L) :
    (ambient f).map g ≫ (ambientCounit f).app L = (ambientCounit f).app K ≫ g :=
  (ambientCounit f).naturality g

/-- Proof debt: when `f` generates `I`, every cohomology module of the specified localized
Cech tensor complex is `I`-power torsion. -/
theorem ambient_mem {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) (K : DerivedCategory (ModuleCat.{u} A)) :
    cohomologyIn (ModuleCat.isIdealPowerTorsion I) ((ambient f).obj K) := sorry

/-- The full-subcategory lift of the specified localized Cech tensor functor. The membership
proof affects only the property field; the underlying objects and morphisms are those of `ambient`. -/
def functor {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion I :=
  (cohomologyIn (ModuleCat.isIdealPowerTorsion I)).lift (ambient f) (ambient_mem I f hgen)

/-- Forgetting the torsion property recovers the specified ambient functor definitionally. -/
def compInclusionIso {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    functor I f hgen ⋙ IdealPowerTorsion.inclusion I ≅ ambient f :=
  (cohomologyIn (ModuleCat.isIdealPowerTorsion I)).liftCompιIso
    (ambient f) (ambient_mem I f hgen)

/-- The forward map for the support-valued functor, using its existing inclusion comparison.
This constructs the forward natural transformation; it does not assert triangle identities
or extract an adjunction record from `adjunction`. -/
def counitForward {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    functor I f hgen ⋙ IdealPowerTorsion.inclusion I ⟶
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  (compInclusionIso I f hgen).hom ≫ ambientCounit f

/-- Proof debt: the specified closed-support functor is right adjoint to the inclusion.
This proposition is not used to construct the functor or to extract any adjunction data. -/
theorem adjunction {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    Nonempty (IdealPowerTorsion.inclusion I ⊣ functor I f hgen) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology.ClosedSupportModel
