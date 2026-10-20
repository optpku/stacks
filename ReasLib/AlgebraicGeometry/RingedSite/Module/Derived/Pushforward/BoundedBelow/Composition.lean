module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of bounded-below derived module pushforwards

The construction is the generic bounded-below right-derived composition comparison, specialized
to the pseudofunctorial composition isomorphism for module pushforward.  Its invertibility uses
only the standard fact that the first pushforward sends injectives to objects acyclic for the
second pushforward.
-/

@[expose] public section

-- Keep these operations on the already specified canonical derived-category model.
-- Local instance justification (defeq pin): ModuleDerived and DerivedCategory.Q must elaborate to the same bundled-ringed-site standard localization; enable the existing reducible moduleCat_hasDerivedCategory owner only for these module comparisons.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

open CategoryTheory

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom.modulePushforwardDerivedPlus

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable {Z : RingedSite.{uZ, vZ, w}}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]

variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
variable [EnoughInjectives (ModuleCat.{z} X)] [EnoughInjectives (ModuleCat.{z} Y)]

/-- The canonical comparison from pushforward along a composite to iterated bounded-below
derived pushforward. -/
@[stacks 015M "bounded derived module-pushforward composition comparison"]
noncomputable def compComparison :
    modulePushforwardDerivedPlus (f.comp g) ⟶
      modulePushforwardDerivedPlus f ⋙ modulePushforwardDerivedPlus g :=
  Functor.RightDerived.Composition.BoundedBelow.comparisonOfIso
    f.modulePushforward g.modulePushforward (modulePushforwardCompIso f g).symm

/-- The bounded derived module-pushforward composition comparison is canonically invertible. -/
@[stacks 015M "bounded derived module-pushforward composition isomorphism"]
theorem compComparison_isIso
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{z})] :
    IsIso (compComparison f g) := sorry

/-- Bounded-below derived module pushforward is pseudofunctorial under composition. -/
@[stacks 015M "bounded derived module-pushforward composition isomorphism"]
noncomputable def compIso [IsIso (compComparison f g)] :
    modulePushforwardDerivedPlus (f.comp g) ≅
      modulePushforwardDerivedPlus f ⋙ modulePushforwardDerivedPlus g :=
  asIso (compComparison f g)

/-- The forward map of `compIso` is the canonical composition comparison. -/
@[simp, stacks 015M "bounded derived module-pushforward composition map"]
theorem compIso_hom [IsIso (compComparison f g)] :
    (compIso f g).hom = compComparison f g := sorry

end RingedSite.Hom.modulePushforwardDerivedPlus
