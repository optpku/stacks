module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Monoidal.Invertible
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- The named ringed-site models unfold to this standard quotient; infer it
-- directly when the site is hidden behind a localized/source ModuleCat alias.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

/-!
# Locally shifted invertible derived modules on ringed sites

An object of the derived category is locally shifted invertible when its restriction to every
member of a suitable cover is a shift of an invertible module.  The bundled ringed-site property
is the canonical owner; the commutative ring-sheaf theorem below identifies it with invertibility
of tensoring on a locally ringed site.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived localizedRestrictionDerived)

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, z}]
variable [∀ U : X.carrier, MonoidalCategory (ModuleCat.{z} (X.localization U))]

/-- Derived module sheaves which are locally shifts of invertible modules, as an object
property. -/
@[stacks 0FPY "local shifted-invertibility object property"]
def locallyShiftedInvertible : ObjectProperty (ModuleDerived.{z} X) :=
  fun M ↦ ∀ U : X.carrier, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ n : ℤ, ∃ L : ModuleCat.{z} (X.localization I.Y),
      Functor.IsEquivalence (tensorRight L) ∧
        IsIsomorphic
          ((localizedRestrictionDerived.{z} X I.Y).obj M)
          (((DerivedCategory.singleFunctor
            (ModuleCat.{z} (X.localization I.Y)) (0 : ℤ)).obj L)⟦-n⟧)

/-- A derived module sheaf is locally shifted invertible when it belongs to
`locallyShiftedInvertible`. -/
@[stacks 0FPY "local shifted-invertibility predicate"]
abbrev IsLocallyShiftedInvertible (M : ModuleDerived.{z} X) : Prop :=
  locallyShiftedInvertible M

/-- Locally shifted invertible derived module sheaves, as a full subcategory. -/
@[stacks 0FPY "local shifted-invertibility full subcategory"]
abbrev LocallyShiftedInvertible :=
  (locallyShiftedInvertible (X := X)).FullSubcategory

namespace LocallyShiftedInvertible

/-- The canonical inclusion of locally shifted invertible derived module sheaves. -/
abbrev ι : LocallyShiftedInvertible (X := X) ⥤ ModuleDerived.{z} X :=
  ObjectProperty.ι _

end LocallyShiftedInvertible

/-- Local shifted invertibility supplies a cover and shifted invertible module on every cover
member. -/
theorem IsLocallyShiftedInvertible.exists_cover
    {M : ModuleDerived.{z} X} (hM : IsLocallyShiftedInvertible M) (U : X.carrier) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      ∃ n : ℤ, ∃ L : ModuleCat.{z} (X.localization I.Y),
        Functor.IsEquivalence (tensorRight L) ∧
          IsIsomorphic
            ((localizedRestrictionDerived.{z} X I.Y).obj M)
            (((DerivedCategory.singleFunctor
              (ModuleCat.{z} (X.localization I.Y)) (0 : ℤ)).obj L)⟦-n⟧) := sorry

/-- Local shifted invertibility is invariant under isomorphisms of derived module sheaves. -/
instance locallyShiftedInvertible_isClosedUnderIsomorphisms :
    (locallyShiftedInvertible (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport local shifted invertibility along an isomorphism. -/
theorem IsLocallyShiftedInvertible.of_iso
    {M N : ModuleDerived.{z} X} (hM : IsLocallyShiftedInvertible M) (e : M ≅ N) :
    IsLocallyShiftedInvertible N := sorry

end RingedSite.Hom.ModuleDerived

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}} [O.IsLocallyRinged]
variable [MonoidalCategory
  (ModuleDerived (RingedSite.ofCommRingSheaf J O))]
variable [∀ U : C,
  MonoidalCategory (ModuleCat ((RingedSite.ofCommRingSheaf J O).localization U))]

/-- On a locally ringed site, a derived module sheaf is invertible exactly when it is locally a shift of an invertible module. -/
@[stacks 0FPY "(3)"]
theorem isInvertible_iff_isLocallyShiftedInvertible
    (M : ModuleDerived (RingedSite.ofCommRingSheaf J O)) :
    isInvertibleObject M ↔
      RingedSite.Hom.ModuleDerived.IsLocallyShiftedInvertible M := sorry

end SheafOfModules.RingedSite
