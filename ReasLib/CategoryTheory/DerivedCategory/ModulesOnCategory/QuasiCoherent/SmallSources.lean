module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Complex.Cardinal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticClosure
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.Bounded
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.SmallSet
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cardinal-bounded sources for quasi-coherent derived modules

This file specializes the cardinal-bounded Brown criterion to the canonical quasi-coherent
subcategory of derived modules on a category with the chaotic topology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open SheafOfModules.RingedSite

universe u v w

namespace CategoryTheory.ModulesOnCategory.Chaotic

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

/-- The least section-cardinality of a complex representing a canonically quasi-coherent
derived module. -/
@[stacks 0GYZ "size of a quasi-coherent derived module"]
def objectCardinal (K : QC 𝒪) : Cardinal.{max (max u v) w} :=
  SheafOfModules.CochainComplex.derivedObjectCardinal
    (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) K.obj

/-- Canonically quasi-coherent derived modules of section-cardinality at most `kappa`. -/
@[stacks 0GYZ "cardinal-bounded quasi-coherent objects"]
def boundedObjects (kappa : Cardinal.{max (max u v) w}) : Set (QC 𝒪) :=
  BrownRepresentability.Bounded.objects (objectCardinal 𝒪) kappa

/-- Every nonzero canonically quasi-coherent derived module receives a nonzero morphism from a
bounded one. -/
def BoundedObjectsDetectNonzero (kappa : Cardinal.{max (max u v) w}) : Prop :=
  BrownRepresentability.Bounded.DetectsNonzeroObjects (objectCardinal 𝒪) kappa

/-- Maps from bounded quasi-coherent objects into countable coproducts factor through
countable coproducts of bounded quasi-coherent objects. -/
def BoundedObjectsFactorCountableCoproducts
    (kappa : Cardinal.{max (max u v) w}) : Prop :=
  BrownRepresentability.Bounded.FactorsThroughCountableCoproducts
    (objectCardinal 𝒪) kappa

/-- Lemma 21.43.8 (0GYZ): one cardinal simultaneously supplies nonzero bounded sources for
all nonzero objects of `QC 𝒪` and bounded componentwise factorizations of maps into countable
coproducts. -/
@[stacks 0GYZ]
theorem exists_cardinal_for_small_sources :
    ∃ kappa : Cardinal.{max (max u v) w},
      BoundedObjectsDetectNonzero 𝒪 kappa ∧
        BoundedObjectsFactorCountableCoproducts 𝒪 kappa := sorry

/-- The two boundedness clauses identify `boundedObjects 𝒪 kappa` as a
Brown-representability set. -/
theorem boundedObjects_isSet
    {kappa : Cardinal.{max (max u v) w}}
    (hdetect : BoundedObjectsDetectNonzero 𝒪 kappa)
    (hfactor : BoundedObjectsFactorCountableCoproducts 𝒪 kappa) :
    BrownRepresentability.IsSet (boundedObjects 𝒪 kappa) := sorry

/-- The canonical quasi-coherent derived category admits a Brown-representability set. -/
@[stacks 0GYZ "Brown-representability set"]
theorem exists_brownSet :
    ∃ S : Set (QC 𝒪), BrownRepresentability.IsSet S := sorry

/-- The cardinal construction supplies representatives forming a Brown set small in the
coefficient universe.  This is the universe-sensitive input used by Brown representability for
the large category `QC 𝒪`. -/
@[stacks 0GYZ "small Brown-representability set"]
theorem exists_smallBrownSet :
    ∃ S : Set (QC 𝒪), Small.{max (max u v) w} S ∧
      BrownRepresentability.IsSet S := sorry

end CategoryTheory.ModulesOnCategory.Chaotic
