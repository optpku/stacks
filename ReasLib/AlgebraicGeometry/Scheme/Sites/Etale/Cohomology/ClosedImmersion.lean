/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DerivedSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ClosedImmersion
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ClosedImmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The support-kernel inclusion is invertible on direct images from the closed subscheme. -/
instance directImage_sectionsWithSupportOnι_isIso :
    IsIso (Functor.whiskerLeft (abelianDirectImage i) (sectionsWithSupportOnι i)) := sorry

/-- The supported subsheaf is isomorphic to the direct image of its inverse image,
using the comparison between affine-presented and continuous direct image. -/
def sectionsWithSupportOnUnitIso :
    sectionsWithSupportOn i ≅ sectionsWithSupport i ⋙ abelianDirectImage i :=
  (Functor.rightUnitor (sectionsWithSupportOn i)).symm ≪≫
    @asIso _ _ _ _
      (Functor.whiskerLeft (sectionsWithSupportOn i) (abelianAdjunction i).unit)
      (@NatIso.isIso_of_isIso_app _ _ _ _ _ _
        (Functor.whiskerLeft (sectionsWithSupportOn i) (abelianAdjunction i).unit)
        (fun F ↦ sectionsWithSupportOn_unit_isIso i F)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (sectionsWithSupport i) (abelianDirectImageIso i)

/-- The unit for direct image and sections with support, obtained by inverting
the inverse-image counit and the support inclusion on direct images. -/
def sectionsWithSupportAdjunctionUnit :
    𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) ⟶
      abelianDirectImage i ⋙ sectionsWithSupport i :=
  (asIso (abelianAdjunctionDirectImage i).counit).inv ≫
    Functor.whiskerRight
      ((Functor.rightUnitor (abelianDirectImage i)).inv ≫
        inv (Functor.whiskerLeft (abelianDirectImage i) (sectionsWithSupportOnι i)))
      (abelianInverseImage i) ≫
    (Functor.associator _ _ _).hom

/-- The counit for direct image and sections with support is the inverse supported
unit followed by the supported-subsheaf inclusion. -/
def sectionsWithSupportAdjunctionCounit :
    sectionsWithSupport i ⋙ abelianDirectImage i ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  (sectionsWithSupportOnUnitIso i).inv ≫ sectionsWithSupportOnι i

/-- The support-adjunction unit and counit satisfy the left triangle identity. -/
theorem sectionsWithSupportAdjunction_left_triangle :
    Functor.whiskerRight (sectionsWithSupportAdjunctionUnit i) (abelianDirectImage i) ≫
      (Functor.associator (abelianDirectImage i) (sectionsWithSupport i)
        (abelianDirectImage i)).hom ≫
      Functor.whiskerLeft (abelianDirectImage i) (sectionsWithSupportAdjunctionCounit i) =
    𝟙 (𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) ⋙ abelianDirectImage i) := sorry

/-- The support-adjunction unit and counit satisfy the right triangle identity. -/
theorem sectionsWithSupportAdjunction_right_triangle :
    Functor.whiskerLeft (sectionsWithSupport i) (sectionsWithSupportAdjunctionUnit i) ≫
      (Functor.associator (sectionsWithSupport i) (abelianDirectImage i)
        (sectionsWithSupport i)).inv ≫
      Functor.whiskerRight (sectionsWithSupportAdjunctionCounit i) (sectionsWithSupport i) =
    𝟙 (sectionsWithSupport i ⋙ 𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})) := sorry

/-- Morphisms from a closed-immersion direct image correspond naturally to morphisms
into sections with support on the closed subscheme. -/
def sectionsWithSupportHomEquiv (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((abelianDirectImage i).obj F ⟶ G) ≃ (F ⟶ (sectionsWithSupport i).obj G) :=
  (Adjunction.mkOfUnitCounit {
    unit := sectionsWithSupportAdjunctionUnit i
    counit := sectionsWithSupportAdjunctionCounit i
    left_triangle := sectionsWithSupportAdjunction_left_triangle i
    right_triangle := sectionsWithSupportAdjunction_right_triangle i }).homEquiv F G

/-- Closed-immersion direct image is left adjoint to sections with support. -/
def sectionsWithSupportAdjunction : abelianDirectImage i ⊣ sectionsWithSupport i :=
  let adj := Adjunction.mkOfUnitCounit {
    unit := sectionsWithSupportAdjunctionUnit i
    counit := sectionsWithSupportAdjunctionCounit i
    left_triangle := sectionsWithSupportAdjunction_left_triangle i
    right_triangle := sectionsWithSupportAdjunction_right_triangle i }
  Adjunction.mkOfHomEquiv {
    homEquiv := sectionsWithSupportHomEquiv i
    homEquiv_naturality_left_symm := adj.homEquiv_naturality_left_symm
    homEquiv_naturality_right := adj.homEquiv_naturality_right }

/-- Sections with support on a closed subscheme are additive, by their direct-image adjunction. -/
instance sectionsWithSupport_additive : (sectionsWithSupport i).Additive :=
  (sectionsWithSupportAdjunction i).right_adjoint_additive

variable [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Exact direct image along a closed immersion is its own total right-derived model. -/
def rightDerivedModel : RightDerivedModel (abelianDirectImage i) :=
  let directImage : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    ⟨abelianDirectImage i, directImage_exact_of_isClosedImmersion i⟩
  Functor.RightDerived.Model.of (derivedDirectImage i)
    directImage.obj.mapDerivedCategoryFactorsh.inv
    (Functor.RightDerived.Exact.isRightDerived directImage.obj)

/-- Every total right-derived model of closed-immersion direct image is isomorphic
to its exact derived action. -/
def derivedDirectImageModelIso (model : RightDerivedModel (abelianDirectImage i)) :
    model.functor ≅ derivedDirectImage i :=
  model.iso (rightDerivedModel i)

/-- The exact inverse-image/direct-image adjunction descends to derived étale categories. -/
def inverseImageAdjunction :
    (abelianInverseImage i).mapDerivedCategory ⊣ derivedDirectImage i :=
  let directImage : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    ⟨abelianDirectImage i, directImage_exact_of_isClosedImmersion i⟩
  Adjunction.mapDerivedCategory (R := directImage.obj) (abelianAdjunctionDirectImage i)

/-- Derived inverse image restricted to supported objects is left adjoint to lifted direct image. -/
def supportedInverseImageAdjunction :
    DerivedSupported.inclusion i ⋙ (abelianInverseImage i).mapDerivedCategory ⊣
      derivedDirectImage.toSupported i :=
  (inverseImageAdjunction i).restrictFullyFaithful
    (derivedSupportedOn i).fullyFaithfulι (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm (derivedDirectImage.toSupportedCompιIso i).symm

/-- The inverse equivalence to closed-immersion derived direct image is restricted inverse image. -/
def supportedQuasiInverse :
    (derivedDirectImage.toSupported i).inv ≅
      DerivedSupported.inclusion i ⋙ (abelianInverseImage i).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    (derivedDirectImage.toSupported i).asEquivalence.symm.toAdjunction
    (supportedInverseImageAdjunction i)

/-- The total right-derived functor of concrete sections with support, computed by K-injectives. -/
def derivedSectionsWithSupport : Derived X ⥤ Derived Z :=
  Functor.RightDerived.KInjective.functor (sectionsWithSupport i)

/-- Lifted derived direct image is left adjoint to restricted derived sections with support. -/
def supportedSectionsAdjunction :
    derivedDirectImage.toSupported i ⊣
      DerivedSupported.inclusion i ⋙ derivedSectionsWithSupport i :=
  (Adjunction.Derived.KInjective.adjunction
    (⟨abelianDirectImage i, directImage_exact_of_isClosedImmersion i⟩ :
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
        Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (sectionsWithSupport i) (sectionsWithSupportAdjunction i)).restrictFullyFaithful
      (Functor.FullyFaithful.id _) (derivedSupportedOn i).fullyFaithfulι
      (derivedDirectImage.toSupportedCompιIso i).symm (Functor.rightUnitor _).symm

/-- Restricted inverse image agrees with restricted total right-derived sections with support. -/
def supportedSectionsQuasiInverseIso :
    DerivedSupported.inclusion i ⋙ (abelianInverseImage i).mapDerivedCategory ≅
      DerivedSupported.inclusion i ⋙ derivedSectionsWithSupport i :=
  (supportedQuasiInverse i).symm ≪≫
    Adjunction.rightAdjointUniq (derivedDirectImage.toSupported i).asEquivalence.toAdjunction
      (supportedSectionsAdjunction i)

end AlgebraicGeometry.Scheme.Etale.ClosedImmersion
