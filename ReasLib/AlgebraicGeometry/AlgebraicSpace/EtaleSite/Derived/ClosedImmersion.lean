module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Model
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionsWithSupport.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Supported
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import Mathlib.CategoryTheory.Adjunction.Unique

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

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image of abelian étale sheaves along a morphism of algebraic spaces is additive. -/
instance sheafInverseImage_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheafInverseImage AddCommGrpCat.{u + 1} f).Additive :=
  (sheafAdjunction AddCommGrpCat.{u + 1} f).left_adjoint_additive

variable {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Small étale pushforward of abelian sheaves along a closed immersion preserves finite limits. -/
instance sheafPushforward_preservesFiniteLimits_of_isClosedImmersion :
    PreservesFiniteLimits (sheafPushforward AddCommGrpCat.{u + 1} i) :=
  inferInstance

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

/-- Every total right-derived model of closed-immersion sheaf pushforward is naturally
isomorphic to its exact action on derived categories. -/
def closedImmersion_etaleDerivedDirectImage_eq_underived
    (closedModel : EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} i)) :
    closedModel.functor ≅ etaleDerivedDirectImage i :=
  closedModel.iso (etaleDerivedDirectImage_rightDerivedModel i)


/-- The inverse of supported derived direct image is naturally isomorphic to restricted
derived inverse image. -/
def closedImmersion_etaleSupported_quasiInverse :
    (etaleDerivedDirectImage.toSupported i).inv ≅ etaleDerivedSupported.inverseImage i :=
  Adjunction.leftAdjointUniq
    (etaleDerivedDirectImage.toSupported i).asEquivalence.symm.toAdjunction
    (etaleDerivedSupported_inverseImageAdjunction i)


/-- The total right-derived functor of sections with support, computed by K-injectives. -/
def etaleDerivedSectionsWithSupport : EtaleDerived X ⥤ EtaleDerived Z :=
by
  refine @Functor.RightDerived.KInjective.functor _ _ _ _ _ _ _ _
    (sectionsWithSupport i) _ ?_ ?_
  · exact ({ } : IsGrothendieckAbelian.{u + 1} (EtaleSheaf X))
  · refine @Functor.RightDerived.KInjective.hasDerived _ _ _ _ _ _ _
      (sectionsWithSupport i) _ ?_
    exact ({ } : IsGrothendieckAbelian.{u + 1} (EtaleSheaf X))

/-- Exact derived direct image is left adjoint to total right-derived sections with support. -/
def etaleDerivedDirectImage_sectionsAdjunction :
    etaleDerivedDirectImage i ⊣ etaleDerivedSectionsWithSupport i :=
  @Adjunction.Derived.KInjective.adjunction _ _ _ _ _ _ _ _
    (⟨sheafPushforward AddCommGrpCat.{u + 1} i,
      ⟨(show PreservesFiniteLimits (sheafPushforward AddCommGrpCat.{u + 1} i) from inferInstance),
        (show PreservesFiniteColimits (sheafPushforward AddCommGrpCat.{u + 1} i) from inferInstance)⟩⟩ :
      EtaleSheaf Z ⥤ₑ EtaleSheaf X)
    (sectionsWithSupport i) _
    (show IsGrothendieckAbelian.{u + 1} (EtaleSheaf X) from { })
    (sectionsWithSupportAdjunction i)

/-- Lifted derived direct image is left adjoint to restricted derived sections with support. -/
def etaleDerivedSupported_sectionsAdjunction :
    etaleDerivedDirectImage.toSupported i ⊣
      EtaleDerivedSupported.inclusion i ⋙ etaleDerivedSectionsWithSupport i :=
  (etaleDerivedDirectImage_sectionsAdjunction i).restrictFullyFaithful
    (Functor.FullyFaithful.id _)
    (etaleDerivedSupportedOn i).fullyFaithfulι
    (etaleDerivedDirectImage.toSupportedCompιIso i).symm
    (Functor.rightUnitor _).symm

/-- Restricted derived inverse image agrees naturally with restricted total right-derived
sections with support. -/
def closedImmersion_etaleSupported_quasiInverse_sections :
    etaleDerivedSupported.inverseImage i ≅
      EtaleDerivedSupported.inclusion i ⋙ etaleDerivedSectionsWithSupport i :=
  (closedImmersion_etaleSupported_quasiInverse i).symm ≪≫
    Adjunction.rightAdjointUniq
      (etaleDerivedDirectImage.toSupported i).asEquivalence.toAdjunction
      (etaleDerivedSupported_sectionsAdjunction i)

end AlgebraicGeometry.AlgebraicSpace
