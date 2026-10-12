/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat.Homology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech-to-derived-sections comparisons

A comparison is a single natural transformation in the bounded-below derived category.  Its
ordinary maps in all nonnegative degrees are obtained by applying homology.  Normalization is a
separate proposition: this prevents an arbitrary derived morphism from being mistaken for the
comparison constructed from an injective resolution.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable {ι : Type u} (cover : ι → Over U)

/-- In nonnegative degree, homology of the derived Cech source canonically recovers ordinary
module-valued Cech cohomology. -/
@[stacks 01EQ "homology of the derived module Cech source"]
noncomputable def derivedSourceHomologyIso (p : ℕ) :
    derivedSource U cover ⋙
        DerivedCategory.Plus.homologyFunctor
          (ModuleCat (sectionsRingOnOpen X U)) (p : ℤ) ≅
      cohomologyFunctor U cover p :=
  Functor.isoWhiskerLeft (complex U cover)
    (CochainComplex.Plus.extendNatDerivedHomologyIso
      (ModuleCat (sectionsRingOnOpen X U)) p)

/-- A coefficient-natural morphism from the Cech complex to bounded-below derived sections. -/
@[stacks 01EQ "derived module Cech comparison datum"]
abbrev Comparison := derivedSource U cover ⟶ derivedTarget U

/-- A degree-`p` Cech-to-derived-cohomology comparison natural in the module sheaf. -/
@[stacks 01EQ "degreewise module Cech comparison datum"]
abbrev DegreeComparison (p : ℕ) :=
  cohomologyFunctor U cover p ⟶ derivedCohomologyFunctor U (p : ℤ)

namespace Comparison

/-- Applying degree-`p` homology to a derived comparison gives a natural transformation of
module-sheaf coefficient functors. -/
@[stacks 01EQ "homology of a derived Cech comparison"]
noncomputable def homology (comparison : Comparison U cover) (p : ℤ) :
    derivedSource U cover ⋙
        DerivedCategory.Plus.homologyFunctor
          (ModuleCat (sectionsRingOnOpen X U)) p ⟶
      derivedTarget U ⋙
        DerivedCategory.Plus.homologyFunctor
          (ModuleCat (sectionsRingOnOpen X U)) p :=
  Functor.whiskerRight comparison
    (DerivedCategory.Plus.homologyFunctor
      (ModuleCat (sectionsRingOnOpen X U)) p)

/-- The degree-`p` comparison obtained by applying homology to one fixed derived comparison. -/
@[stacks 01EQ "degreewise module Cech comparison"]
noncomputable def degree
    (comparison : Comparison U cover) (p : ℕ) : DegreeComparison U cover p :=
  (derivedSourceHomologyIso U cover p).inv ≫
    Comparison.homology U cover comparison (p : ℤ)

/-- The component of a fixed comparison at a module sheaf in degree `p`. -/
@[stacks 01EQ "degreewise Cech comparison component"]
abbrev app
    (comparison : Comparison U cover) (F : X.Modules) (p : ℕ) :
    cohomology U cover F p ⟶ (derivedCohomologyFunctor U (p : ℤ)).obj F :=
  (Comparison.degree U cover comparison p).app F

/-- A comparison is invertible at a coefficient sheaf when all its nonnegative-degree
projections at that sheaf are invertible. -/
@[stacks 01EQ "invertibility of a derived module Cech comparison"]
def IsIsoAt (comparison : Comparison U cover) (F : X.Modules) : Prop :=
  ∀ p : ℕ, IsIso (Comparison.app U cover comparison F p)

/-- The component isomorphism supplied by an objectwise invertibility certificate.  The
certificate is consumed explicitly, so downstream statements do not need a proof-local instance
in order to use the inverse. -/
@[stacks 01EQ "objectwise Cech comparison isomorphism"]
noncomputable def IsIsoAt.appIso
    {comparison : Comparison U cover} {F : X.Modules}
    (h : Comparison.IsIsoAt U cover comparison F) (p : ℕ) :
    cohomology U cover F p ≅ (derivedCohomologyFunctor U (p : ℤ)).obj F :=
  @asIso _ _ _ _ (Comparison.app U cover comparison F p) (h p)

/-- The object-level `IsIsomorphic` view of an invertible Cech comparison component. -/
@[stacks 01EQ "objectwise Cech comparison isomorphic component"]
theorem IsIsoAt.isIsomorphic_app
    {comparison : Comparison U cover} {F : X.Modules}
    (h : Comparison.IsIsoAt U cover comparison F) (p : ℕ) :
    IsIsomorphic (cohomology U cover F p)
      ((derivedCohomologyFunctor U (p : ℤ)).obj F) := sorry

/-- An invertible Cech comparison component identifies Cech cohomology with the ordinary
right-derived cohomology of sections. -/
@[stacks 01EN "Cech comparison with ordinary right-derived cohomology"]
theorem IsIsoAt.isIsomorphic_rightDerived
    {comparison : Comparison U cover} {F : X.Modules}
    (h : Comparison.IsIsoAt U cover comparison F) (p : ℕ) :
    IsIsomorphic (cohomology U cover F p)
      ((moduleCohomologyAtOpenFunctor X U p).obj F) := sorry

/-- A derived comparison is normalized when its degree-zero projection is invertible for every
coefficient sheaf. -/
@[stacks 01EQ "normalization of a derived module Cech comparison"]
def IsNormalized (comparison : Comparison U cover) : Prop :=
  ∀ F : X.Modules, IsIso (Comparison.app U cover comparison F 0)

/-- A normalized comparison is invertible in degree zero at every coefficient sheaf. -/
@[stacks 01EQ "normalized degree-zero Cech comparison invertibility"]
theorem IsNormalized.app_zero_isIso
    {comparison : Comparison U cover} (h : Comparison.IsNormalized U cover comparison)
    (F : X.Modules) : IsIso (Comparison.app U cover comparison F 0) := sorry

/-- The degree-zero isomorphism supplied by a normalized comparison.  The invertibility proof is
consumed explicitly, so callers need no proof-local `IsIso` instance. -/
@[stacks 01EQ "degree-zero normalized Cech comparison isomorphism"]
noncomputable def IsNormalized.zeroIso
    {comparison : Comparison U cover} (h : Comparison.IsNormalized U cover comparison)
    (F : X.Modules) :
    cohomology U cover F 0 ≅ (derivedCohomologyFunctor U 0).obj F :=
  @asIso _ _ _ _ (Comparison.app U cover comparison F 0) (h F)

/-- The object-level `IsIsomorphic` view of a normalized degree-zero comparison. -/
@[stacks 01EQ "degree-zero normalized Cech comparison"]
theorem IsNormalized.zero_isIsomorphic
    {comparison : Comparison U cover} (h : Comparison.IsNormalized U cover comparison)
    (F : X.Modules) :
    IsIsomorphic (cohomology U cover F 0)
      ((derivedCohomologyFunctor U 0).obj F) := sorry

/-- A normalized degree-zero comparison identifies zeroth Cech cohomology with ordinary zeroth
right-derived cohomology of sections. -/
@[stacks 01EN "degree-zero Cech comparison with ordinary right-derived cohomology"]
theorem IsNormalized.zero_isIsomorphic_rightDerived
    {comparison : Comparison U cover} (h : Comparison.IsNormalized U cover comparison)
    (F : X.Modules) :
    IsIsomorphic (cohomology U cover F 0)
      ((moduleCohomologyAtOpenFunctor X U 0).obj F) := sorry

/-- A covering family admits a normalized coefficient-natural transformation from its Cech
complex to bounded-below derived sections. -/
@[stacks 01EQ "derived module Cech comparison"]
theorem exists_normalized
    (hcover : ((Opens.grothendieckTopology X.carrier).over U).CoversTop cover) :
    ∃ comparison : Comparison U cover,
      Comparison.IsNormalized U cover comparison := sorry

/-- An indexed open family with supremum `U` supplies the slice-cover hypothesis automatically. -/
@[stacks 01EQ "normalized Cech comparison for an indexed open cover"]
theorem exists_normalized_of_iSup_eq
    {U : Opens X.carrier} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) :
    ∃ comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰),
      Comparison.IsNormalized U (Opens.Cover.overFamily U 𝒰 h𝒰) comparison := sorry

end Comparison

/-- Homology of bounded-below derived sections in a nonnegative degree is isomorphic to the
ordinary injective-resolution cohomology functor. -/
@[stacks 01EQ "bounded derived sections compute module cohomology"]
theorem derivedTarget_homology_isIsomorphic (p : ℕ) :
    IsIsomorphic
      (derivedTarget U ⋙
        DerivedCategory.Plus.homologyFunctor
          (ModuleCat (sectionsRingOnOpen X U)) (p : ℤ))
      (moduleCohomologyAtOpenFunctor X U p) := sorry

/-- Canonical bounded-derived cohomology agrees, in a nonnegative degree, with the ordinary
injective-resolution right-derived functor. -/
@[stacks 01EN "bounded and ordinary module right-derived cohomology"]
theorem derivedCohomologyFunctor_isIsomorphic_rightDerived (p : ℕ) :
    IsIsomorphic (derivedCohomologyFunctor U (p : ℤ))
      (moduleCohomologyAtOpenFunctor X U p) := sorry

end AlgebraicGeometry.RingedSpace.ModuleCech

