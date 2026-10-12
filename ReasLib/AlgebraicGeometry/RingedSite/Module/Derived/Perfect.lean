/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Perfect

@[expose] public section

/-!
# Perfect derived modules on ringed sites

This module owns perfectness after passage to the derived category.  The complex-level property
and its full subcategory live in `Module/Complex/Perfect.lean`; a derived object is perfect when it
admits a representative from that property.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite.Hom

noncomputable section

universe u v w


namespace RingedSite

section PerfectDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace Hom.ModuleDerived

/-- Perfect derived module sheaves on a ringed site, as an object property. -/
def perfect : ObjectProperty (ModuleDerived.{w} X) :=
  fun K ↦ ∃ E : CochainComplex (ModuleCat.{w} X) ℤ,
    ∃ _ : K ≅ (@DerivedCategory.Q
      (ModuleCat.{w} X) inferInstance inferInstance
      (Hom.moduleCat_hasDerivedCategory X)).obj E,
      RingedSite.CochainComplex.IsPerfect E

/-- A derived object of modules on a ringed site is perfect when it is isomorphic to the image
of a perfect complex under the derived-category localization functor. -/
@[stacks 08G5]
abbrev IsPerfect (K : ModuleDerived.{w} X) : Prop :=
  perfect (X := X) K

/-- Perfect derived module sheaves, as a full subcategory. -/
@[stacks 08G5 "(2), full subcategory"]
abbrev Perfect :=
  (perfect (X := X)).FullSubcategory

namespace Perfect

/-- The canonical inclusion of perfect derived module sheaves on a ringed site. -/
abbrev ι : Perfect (X := X) ⥤ ModuleDerived.{w} X :=
  ObjectProperty.ι _

end Perfect

/-- Perfectness of a derived module sheaf is equivalent to the existence of a perfect complex
representative. -/
theorem isPerfect_iff_exists_perfect_representative (K : ModuleDerived.{w} X) :
    IsPerfect K ↔
      ∃ E : CochainComplex (ModuleCat.{w} X) ℤ,
        ∃ _ : K ≅ (@DerivedCategory.Q
          (ModuleCat.{w} X) inferInstance inferInstance
          (Hom.moduleCat_hasDerivedCategory X)).obj E,
        RingedSite.CochainComplex.IsPerfect E := sorry

/-- An isomorphism to the localization of a perfect complex exhibits a perfect derived object. -/
theorem of_iso_q_obj
    {K : ModuleDerived.{w} X} {E : CochainComplex (ModuleCat.{w} X) ℤ}
    (e : K ≅ (@DerivedCategory.Q
      (ModuleCat.{w} X) inferInstance inferInstance
      (Hom.moduleCat_hasDerivedCategory X)).obj E)
    (hE : RingedSite.CochainComplex.IsPerfect E) :
    IsPerfect K := sorry

/-- Perfectness of derived module sheaves transports along isomorphisms. -/
theorem IsPerfect.of_iso {K L : ModuleDerived.{w} X} (hK : IsPerfect K) (e : K ≅ L) :
    IsPerfect L := sorry

/-- A perfect derived object admits a perfect complex representative. -/
theorem exists_perfect_representative {K : ModuleDerived.{w} X} (hK : IsPerfect K) :
    ∃ E : CochainComplex (ModuleCat.{w} X) ℤ,
      ∃ _ : K ≅ (@DerivedCategory.Q
        (ModuleCat.{w} X) inferInstance inferInstance
        (Hom.moduleCat_hasDerivedCategory X)).obj E,
        RingedSite.CochainComplex.IsPerfect E := sorry

/-- Every complex representing a perfect derived module sheaf is perfect. -/
@[stacks 08G6 "(2)"]
theorem IsPerfect.of_representation
    {K : ModuleDerived.{w} X} (hK : IsPerfect K)
    {E : CochainComplex (ModuleCat.{w} X) ℤ}
    (e : K ≅ (@DerivedCategory.Q
      (ModuleCat.{w} X) inferInstance inferInstance
      (Hom.moduleCat_hasDerivedCategory X)).obj E) :
    RingedSite.CochainComplex.IsPerfect E := sorry

/-- Perfect derived objects on a ringed site are stable under isomorphism. -/
theorem perfect_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (RingedSite.Hom.ModuleDerived.IsPerfect : ObjectProperty (ModuleDerived.{w} X)) := sorry

end Hom.ModuleDerived

end PerfectDerived

end RingedSite
