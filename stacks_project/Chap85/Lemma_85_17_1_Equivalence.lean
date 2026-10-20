module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import stacks_project.Chap85.Lemma_85_17_1_Cartesian

/-!
# Hypercovering descent equivalence for sheaves

If `K` is a hypercovering of the terminal presheaf, then `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)`
is fully faithful with essential image the cartesian sheaves, and `a_*` is a quasi-inverse.
The same statement holds for abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify J A]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ A,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- The adjunction `a⁻¹ ⊣ a_*` presented by the continuous and cocontinuous functor
`j_total`. -/
def sheafLocalizationAdjunction :
    inverseImage J K.simplicial A ⊣ directImage J K.simplicial A :=
  (totalForget K.simplicial).sheafAdjunctionCocontinuous A
    (overSiteTotalTopology J K.simplicial) J

/-- `sheafLocalizationAdjunction` is `sheafAdjunctionCocontinuous` of `j_total`. -/
theorem sheafLocalizationAdjunction_eq :
    sheafLocalizationAdjunction J K A =
      (totalForget K.simplicial).sheafAdjunctionCocontinuous A
        (overSiteTotalTopology J K.simplicial) J :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering is full. -/
instance inverseImage_full : (inverseImage J K.simplicial A).Full :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering is faithful. -/
instance inverseImage_faithful : (inverseImage J K.simplicial A).Faithful :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering is fully faithful. -/
def inverseImage_fullyFaithful : (inverseImage J K.simplicial A).FullyFaithful :=
  FullyFaithful.ofFullyFaithful _

/-- The unit of `a⁻¹ ⊣ a_*` is an isomorphism. -/
theorem unit_app_isIso (F : Sheaf J A) :
    IsIso ((sheafLocalizationAdjunction J K A).unit.app F) :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism precisely on cartesian sheaves. -/
theorem counit_app_isIso_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) A) :
    IsIso ((sheafLocalizationAdjunction J K A).counit.app G) ↔
      IsCartesian J K.simplicial A G :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism on a cartesian sheaf. -/
theorem counit_app_isIso_of_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) A)
    (h : IsCartesian J K.simplicial A G) :
    IsIso ((sheafLocalizationAdjunction J K A).counit.app G) :=
  sorry

/-- A sheaf on `(C / K)_total` lies in the essential image of `a⁻¹` if and only if it is
cartesian. -/
theorem mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) A) :
    (inverseImage J K.simplicial A).essImage G ↔ IsCartesian J K.simplicial A G :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian sheaves on `(C / K)_total`. -/
def cartesianFunctor : Sheaf J A ⥤ Cartesian J K.simplicial A :=
  (cartesianProperty J K.simplicial A).lift (inverseImage J K.simplicial A)
    fun F ↦ inverseImage_isCartesian J K.simplicial A F

/-- On objects, `cartesianFunctor` is inverse image along `j_total`. -/
theorem cartesianFunctor_obj (F : Sheaf J A) :
    ((cartesianFunctor J K A).obj F).obj = (inverseImage J K.simplicial A).obj F :=
  sorry

/-- The functor sending a cartesian sheaf on `(C / K)_total` to `a_*` of its underlying
sheaf. -/
def cartesianInverse : Cartesian J K.simplicial A ⥤ Sheaf J A :=
  (cartesianProperty J K.simplicial A).ι ⋙ directImage J K.simplicial A

/-- On objects, `cartesianInverse` is direct image along `j_total`. -/
theorem cartesianInverse_obj (G : Cartesian J K.simplicial A) :
    (cartesianInverse J K A).obj G = (directImage J K.simplicial A).obj G.obj :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ a_*` of hypercovering descent. -/
def cartesianUnitIso :
    𝟭 (Sheaf J A) ≅ cartesianFunctor J K A ⋙ cartesianInverse J K A :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _ ((sheafLocalizationAdjunction J K A).unit.app F)
        (unit_app_isIso J K A F))
    sorry

/-- The component of `cartesianUnitIso` at `F` is the adjunction unit. -/
theorem cartesianUnitIso_hom_app (F : Sheaf J A) :
    (cartesianUnitIso J K A).hom.app F =
      (sheafLocalizationAdjunction J K A).unit.app F :=
  sorry

/-- The counit isomorphism `a_* ⋙ a⁻¹ ≅ 𝟭` on cartesian sheaves. -/
def cartesianCounitIso :
    cartesianInverse J K A ⋙ cartesianFunctor J K A ≅ 𝟭 (Cartesian J K.simplicial A) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty J K.simplicial A).isoMk
        (@asIso _ _ _ _ ((sheafLocalizationAdjunction J K A).counit.app G.obj)
          (counit_app_isIso_of_isCartesian J K A G.obj G.property)))
    sorry

/-- The component of `cartesianCounitIso` at `G` is the adjunction counit on the underlying
sheaf. -/
theorem cartesianCounitIso_hom_app_hom (G : Cartesian J K.simplicial A) :
    ((cartesianCounitIso J K A).hom.app G).hom =
      (sheafLocalizationAdjunction J K A).counit.app G.obj :=
  sorry

/-- If `K` is a hypercovering of the terminal presheaf, then `a⁻¹` implements an equivalence
between sheaves on `C` and cartesian sheaves on `(C / K)_total`, with quasi-inverse `a_*`. -/
def cartesianEquivalence : Sheaf J A ≌ Cartesian J K.simplicial A :=
  Equivalence.mk (cartesianFunctor J K A) (cartesianInverse J K A)
    (cartesianUnitIso J K A) (cartesianCounitIso J K A)

/-- The forward functor of `cartesianEquivalence` is `a⁻¹` corestricted to cartesian sheaves. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence J K A).functor = cartesianFunctor J K A :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian sheaves. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence J K A).inverse = cartesianInverse J K A :=
  sorry

end CategoryTheory.SemiRepresentableFamily
