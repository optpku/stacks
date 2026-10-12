/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ClosedImmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- An abelian étale sheaf is supported on a closed subscheme when its restriction
to the complementary open subscheme is zero. -/
abbrev sheafSupportedOn : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  fun F ↦ IsZero
    ((etaleRestrictionSheaf (closedImmersionComplement i).ι AddCommGrpCat.{u}).obj F)

/-- Support on a closed subscheme is equivalent to vanishing on its open complement. -/
theorem sheafSupportedOn_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    sheafSupportedOn i F ↔ IsZero
      ((etaleRestrictionSheaf (closedImmersionComplement i).ι AddCommGrpCat.{u}).obj F) := sorry

/-- Direct image along a closed immersion preserves finite limits. -/
instance directImage_preservesFiniteLimits : PreservesFiniteLimits (abelianDirectImage i) :=
  (directImage_exact_of_isClosedImmersion i).1

/-- Direct image along a closed immersion preserves finite colimits. -/
instance directImage_preservesFiniteColimits : PreservesFiniteColimits (abelianDirectImage i) :=
  (directImage_exact_of_isClosedImmersion i).2

variable [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- A derived étale object is supported on a closed subscheme when all its
integer-degree cohomology sheaves vanish on the open complement. -/
abbrev derivedSupportedOn : ObjectProperty (Derived X) :=
  DerivedCategory.cohomologyIn (sheafSupportedOn i)

/-- The full subcategory of derived étale objects supported on a closed subscheme. -/
abbrev DerivedSupported := (derivedSupportedOn i).FullSubcategory

/-- The inclusion of the supported derived étale category into the ambient category. -/
abbrev DerivedSupported.inclusion : DerivedSupported i ⥤ Derived X :=
  (derivedSupportedOn i).ι

/-- The derived action of exact direct image along a closed immersion. -/
abbrev derivedDirectImage : Derived Z ⥤ Derived X :=
  ExactFunctor.mapDerivedCategory (⟨abelianDirectImage i, directImage_exact_of_isClosedImmersion i⟩ :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- Derived direct image along a closed immersion has supported cohomology sheaves. -/
theorem derivedDirectImage_obj_supported (K : Derived Z) :
    derivedSupportedOn i ((derivedDirectImage i).obj K) := sorry

/-- The essential image of derived direct image along a closed immersion consists
exactly of objects with supported cohomology sheaves. -/
theorem derivedDirectImage_mem_essImage_iff_supported (K : Derived X) :
    (derivedDirectImage i).essImage K ↔ derivedSupportedOn i K := sorry

/-- Derived direct image along a closed immersion, with its cohomological support retained. -/
abbrev derivedDirectImage.toSupported : Derived Z ⥤ DerivedSupported i :=
  (derivedSupportedOn i).lift (derivedDirectImage i) (derivedDirectImage_obj_supported i)

/-- Forgetting support after lifted derived direct image recovers the ambient direct image. -/
def derivedDirectImage.toSupportedCompιIso :
    derivedDirectImage.toSupported i ⋙ DerivedSupported.inclusion i ≅ derivedDirectImage i :=
  (derivedSupportedOn i).liftCompιIso (derivedDirectImage i) (derivedDirectImage_obj_supported i)

namespace derivedDirectImage

/-- Derived direct image along a closed immersion is an equivalence onto supported objects. -/
theorem toSupported_isEquivalence :
    (derivedDirectImage.toSupported i).IsEquivalence := sorry

attribute [instance] toSupported_isEquivalence

end derivedDirectImage

end AlgebraicGeometry.Scheme.Etale.ClosedImmersion
