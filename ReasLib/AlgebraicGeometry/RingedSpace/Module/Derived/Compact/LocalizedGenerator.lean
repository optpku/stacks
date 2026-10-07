module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Dimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Generators
public import ReasLib.CategoryTheory.Preadditive.CompactObject

@[expose] public section

/-!
# Compact localized generators in the derived category

The underived localized generator is the lower-shriek extension `j_!𝒪_U`.  Its canonical
degree-zero realization is the source object for the open-cohomology compactness criterion.
-/

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

/-- The localized structure-module generator `j_!𝒪_U`, placed in cohomological degree zero. -/
@[stacks 0F5Z "canonical degree-zero object"]
noncomputable abbrev localizedGenerator
    (X : RingedSpace.{u}) (U : Opens X.carrier) : ModuleDerived X :=
  (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
    (Modules.localizedGenerator X U)

namespace LocalizedGenerator

/-- Lemma 20.53.1 (0F5Z): if module cohomology on `U` vanishes above a uniform bound and every
degree commutes with arbitrary coproducts, then `j_!𝒪_U[0]` is compact in `D(𝒪_X)`. -/
@[stacks 0F5Z]
theorem isCompactObject {X : RingedSpace.{u}} {U : Opens X.carrier}
    (hvanish : ModuleCohomology.HasFiniteDimension X U)
    (hcoproduct : ModuleCohomology.PreservesCoproducts X U) :
    IsCompactObject (localizedGenerator X U) := sorry

end LocalizedGenerator

end AlgebraicGeometry.RingedSpace.ModuleDerived
