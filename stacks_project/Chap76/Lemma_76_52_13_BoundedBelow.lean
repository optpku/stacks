module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus

/-!
# Locally bounded-below derived modules on algebraic spaces

Local boundedness below on `D(𝒪_X)` is tested on étale scheme charts, reducing to the
ringed-space predicate `RingedSpace.ModuleDerived.IsLocallyBoundedBelow` after
`restrictToSchemeDerived`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A derived `𝒪_X`-module is locally bounded below when, after derived pullback to every
étale scheme chart, the transported restriction is locally bounded below on the underlying
ringed space. -/
def locallyBoundedBelow : ObjectProperty (ModuleDerived X) :=
  fun E ↦
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ],
      RingedSpace.ModuleDerived.IsLocallyBoundedBelow
        (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
          ((restrictToSchemeDerived U).obj ((pullback φ).obj E)))

/-- A derived `𝒪_X`-module is locally bounded below when it belongs to
`locallyBoundedBelow`. -/
abbrev IsLocallyBoundedBelow (E : ModuleDerived X) : Prop :=
  locallyBoundedBelow E

/-- Local boundedness below on an algebraic space unfolds to the étale-local ringed-space
condition on scheme charts. -/
theorem isLocallyBoundedBelow_iff (E : ModuleDerived X) :
    IsLocallyBoundedBelow E ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ],
        RingedSpace.ModuleDerived.IsLocallyBoundedBelow
          (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
            ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) :=
  sorry

/-- Local boundedness below implies the ringed-space condition after restriction to every
étale scheme chart. -/
theorem IsLocallyBoundedBelow.etale {E : ModuleDerived X} (hE : IsLocallyBoundedBelow E)
    (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ] :
    RingedSpace.ModuleDerived.IsLocallyBoundedBelow
      (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
        ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
