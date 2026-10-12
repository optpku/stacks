/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Model
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap67.Lemma_67_13_5_Adjunction
public import stacks_project.Chap69.Lemma_69_9_4_Supported

/-!
# Derived small-étale pushforward along a closed immersion of algebraic spaces

The exact functor `i_*` on abelian étale sheaves induces `etaleDerivedDirectImage` on
derived categories, which lifts to an equivalence onto `D_|Z|(X_étale)` with specified
quasi-inverse the restriction of `i⁻¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image of abelian étale sheaves along a morphism of algebraic spaces is additive. -/
instance sheafInverseImage_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafInverseImage AddCommGrpCat.{u + 1} f).Additive :=
  sorry

/-- An explicit total right-derived model of an additive functor between categories of
abelian étale sheaves on algebraic spaces. -/
abbrev EtaleRightDerivedModel {X Y : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Y)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Y)]
    (F : EtaleSheaf X ⥤ EtaleSheaf Y) [F.Additive] :=
  Model
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ etaleDerivedQuotient Y)
    (etaleDerivedQuotient X) (etaleQuasiIso X)

variable {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Small étale pushforward of abelian sheaves along a closed immersion preserves finite limits. -/
instance sheafPushforward_preservesFiniteLimits_of_isClosedImmersion :
    PreservesFiniteLimits (sheafPushforward AddCommGrpCat.{u + 1} i) :=
  sorry

/-- Small étale pushforward of abelian sheaves along a closed immersion preserves finite
colimits. -/
instance sheafPushforward_preservesFiniteColimits_of_isClosedImmersion :
    PreservesFiniteColimits (sheafPushforward AddCommGrpCat.{u + 1} i) :=
  sorry

variable [Etale (closedImmersionComplementι i)]
variable [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Z)]
variable [Abelian (EtaleSheaf (closedImmersionComplement i))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Z)]
variable [(sheafPushforward AddCommGrpCat.{u + 1} i).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} i).Additive]

/-- The derived small-étale direct image of a closed immersion, obtained as
`mapDerivedCategory` of the exact functor `sheafPushforward i`. Because `i_*` is exact,
this is also `Ri_*`. -/
abbrev etaleDerivedDirectImage : EtaleDerived Z ⥤ EtaleDerived X :=
  (sheafPushforward AddCommGrpCat.{u + 1} i).mapDerivedCategory

/-- The underived exact presentation of `sheafPushforward i` as an explicit right-derived
model, exhibiting `etaleDerivedDirectImage i` as `Ri_*`. -/
def etaleDerivedDirectImage_rightDerivedModel :
    EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} i) :=
  Model.of
    (etaleDerivedDirectImage i)
    (sheafPushforward AddCommGrpCat.{u + 1} i).mapDerivedCategoryFactorsh.inv
    (Exact.isRightDerived (sheafPushforward AddCommGrpCat.{u + 1} i))

/-- Derived small-étale direct image of a closed immersion has cohomology supported
on the closed image. -/
theorem etaleDerivedDirectImage_obj_supported (K : EtaleDerived Z) :
    etaleDerivedSupportedOn i ((etaleDerivedDirectImage i).obj K) :=
  sorry

/-- An ambient étale derived object lies in the essential image of derived small-étale
direct image if and only if its cohomology is supported on the closed image of `i`. -/
theorem etaleDerivedDirectImage_mem_essImage_iff_supported (K : EtaleDerived X) :
    (etaleDerivedDirectImage i).essImage K ↔ etaleDerivedSupportedOn i K :=
  sorry

/-- Derived small-étale direct image lifted to the supported subcategory `D_|Z|(X_étale)`. -/
abbrev etaleDerivedDirectImage.toSupported :
    EtaleDerived Z ⥤ EtaleDerivedSupported i :=
  (etaleDerivedSupportedOn i).lift (etaleDerivedDirectImage i)
    (etaleDerivedDirectImage_obj_supported i)

/-- Forgetting the support witness after lifted direct image recovers derived
small-étale direct image. -/
def etaleDerivedDirectImage.toSupportedCompιIso :
    etaleDerivedDirectImage.toSupported i ⋙ EtaleDerivedSupported.inclusion i ≅
      etaleDerivedDirectImage i :=
  (etaleDerivedSupportedOn i).liftCompιIso (etaleDerivedDirectImage i)
    (etaleDerivedDirectImage_obj_supported i)

/-- The restriction of derived inverse image `i⁻¹` to `D_|Z|(X_étale)`. -/
abbrev etaleDerivedSupported.inverseImage :
    EtaleDerivedSupported i ⥤ EtaleDerived Z :=
  EtaleDerivedSupported.inclusion i ⋙
    (sheafInverseImage AddCommGrpCat.{u + 1} i).mapDerivedCategory

/-- Derived adjunction `i⁻¹ ⊣ i_*` on étale derived categories of algebraic spaces. -/
def etaleDerivedInverseImageAdjunction :
    (sheafInverseImage AddCommGrpCat.{u + 1} i).mapDerivedCategory ⊣
      etaleDerivedDirectImage i :=
  Adjunction.mapDerivedCategory (sheafAdjunction AddCommGrpCat.{u + 1} i)

/-- Restriction of `i⁻¹ ⊣ i_*` to the supported subcategory `D_|Z|(X_étale)`. -/
def etaleDerivedSupported_inverseImageAdjunction :
    etaleDerivedSupported.inverseImage i ⊣ etaleDerivedDirectImage.toSupported i :=
  (etaleDerivedInverseImageAdjunction i).restrictFullyFaithful
    (etaleDerivedSupportedOn i).fullyFaithfulι
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (etaleDerivedDirectImage.toSupportedCompιIso i).symm

/-- The unit of the supported inverse-image adjunction is an isomorphism. -/
instance isIso_unit_etaleDerivedSupported_inverseImageAdjunction :
    IsIso (etaleDerivedSupported_inverseImageAdjunction i).unit :=
  sorry

/-- The counit of the supported inverse-image adjunction is an isomorphism. -/
instance isIso_counit_etaleDerivedSupported_inverseImageAdjunction :
    IsIso (etaleDerivedSupported_inverseImageAdjunction i).counit :=
  sorry

/-- Lifted derived small-étale direct image is an equivalence onto `D_|Z|(X_étale)`,
with specified inverse `etaleDerivedSupported.inverseImage`. -/
instance etaleDerivedDirectImage.toSupported_isEquivalence :
    (etaleDerivedDirectImage.toSupported i).IsEquivalence :=
  (etaleDerivedSupported_inverseImageAdjunction i).toEquivalence.isEquivalence_inverse

end AlgebraicGeometry.AlgebraicSpace
