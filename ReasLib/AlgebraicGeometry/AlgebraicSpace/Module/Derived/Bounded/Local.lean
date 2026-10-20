module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Locally bounded-below derived modules on algebraic spaces

Local boundedness below is expressed by vanishing of cohomology sheaves after restriction
to covering domains of the small étale site, with a lower bound on each domain.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A derived module is locally bounded below if every object of the small étale site has
a covering on whose domains its cohomology sheaves vanish below an integer bound. -/
def locallyBoundedBelow : ObjectProperty (ModuleDerived X) :=
  fun E ↦ ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
    ∃ n : ℤ, ∀ i : ℤ, i < n → CategoryTheory.Limits.IsZero
      ((SheafOfModules.Localization.restriction (structureSheaf X) I.Y).obj
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E))

/-- A derived `𝒪_X`-module is locally bounded below when it belongs to
`locallyBoundedBelow`. -/
abbrev IsLocallyBoundedBelow (E : ModuleDerived X) : Prop :=
  locallyBoundedBelow E

/-- Local boundedness below is equivalent to vanishing of cohomology sheaves below a
bound on each domain of a covering of every object of the small étale site. -/
theorem isLocallyBoundedBelow_iff (E : ModuleDerived X) :
    IsLocallyBoundedBelow E ↔
      ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
        ∃ n : ℤ, ∀ i : ℤ, i < n → CategoryTheory.Limits.IsZero
          ((SheafOfModules.Localization.restriction (structureSheaf X) I.Y).obj
            ((DerivedCategory.homologyFunctor (Modules X) i).obj E)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
