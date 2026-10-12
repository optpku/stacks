/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Spectral.Prespectral
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Dimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Bounded
public import ReasLib.CategoryTheory.Preadditive.CompactObject.Relative

@[expose] public section

/-!
# Compactness of perfect derived modules

This leaf owns the two compactness statements for perfect complexes on quasi-compact,
quasi-separated ringed spaces with a basis of quasi-compact opens.  Relative compactness tests
ambient coproducts whose apex is bounded below; it does not form coproducts in the bounded-below
subcategory.
-/

open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [CompactSpace X.carrier] [PrespectralSpace X.carrier]
variable [QuasiSeparatedSpace X.carrier]

/-- Lemma 20.53.2 (09J7) (1): a perfect derived module is compact relative to ambient
coproducts whose coproduct object is bounded below. -/
@[stacks 09J7 "(1)"]
theorem IsPerfect.isCompactOnBoundedBelow
    {K : ModuleDerived X} (hK : IsPerfect K) :
    IsCompactObjectOn (t.plus : ObjectProperty (ModuleDerived X)) K := sorry

/-- Lemma 20.53.2 (09J7) (2): finite module-cohomological dimension upgrades every perfect
derived module to an ambient compact object. -/
@[stacks 09J7 "(2)"]
theorem IsPerfect.isCompactObject
    {K : ModuleDerived X} (hK : IsPerfect K)
    (hX : Module.HasFiniteCohomologicalDimension X) :
    IsCompactObject K := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
