/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap98.«98_9_3_1_Approximation»
public import stacks_project.Chap110.Proposition_110_72_5
public import stacks_project.Chap110.Proposition_110_72_5_HomStack

/-!
# Non-essential-surjectivity of restriction for a Hom-stack

In the setup of Stacks 110.72, the canonical restriction from the fibre of the
Hom-stack over `S = specPowerSeries k` to formal objects over the truncations of
`k⟦t⟧` is not essentially surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupScheme
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.Hom
open Functor.Fiber
open IsLocalRing
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- The power series ring `k⟦t⟧` is a complete local ring. -/
instance instIsCompleteLocalRing_powerSeries {k : Type u} [Field k] :
    IsCompleteLocalRing (PowerSeries k) :=
  sorry

/-- The spectrum of the formal power series ring `k⟦t⟧` is locally Noetherian. -/
instance instIsLocallyNoetherian_specPowerSeries {k : Type u} [Field k] :
    IsLocallyNoetherian (specPowerSeries k) :=
  sorry

/-- The residue-field morphism `Spec k ⟶ specPowerSeries k` is locally of finite
type. -/
theorem powerSeriesAlgebra_residue_locallyOfFiniteType {k : Type u} [Field k] :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal (PowerSeries k)))) ≫
        𝟙 (specPowerSeries k)) :=
  sorry

/-- The complete local `specPowerSeries k`-algebra with carrier `k⟦t⟧` and
structure morphism `𝟙 (specPowerSeries k)`. -/
def powerSeriesAlgebra (k : Type u) [Field k] :
    CompleteLocalSAlgebra (specPowerSeries k) :=
  CompleteLocalSAlgebra.of (PowerSeries k) (𝟙 (specPowerSeries k))
    powerSeriesAlgebra_residue_locallyOfFiniteType

/-- The carrier of `powerSeriesAlgebra k` is `k⟦t⟧`. -/
theorem powerSeriesAlgebra_carrier (k : Type u) [Field k] :
    (powerSeriesAlgebra k).carrier = PowerSeries k :=
  sorry

/-- The structure morphism of `powerSeriesAlgebra k` is `𝟙 (specPowerSeries k)`. -/
theorem powerSeriesAlgebra_toS (k : Type u) [Field k] :
    (powerSeriesAlgebra k).toS = 𝟙 (specPowerSeries k) :=
  sorry

/-- Formal objects of a groupoid fibration over `specPowerSeries k` whose complete
local algebra is `powerSeriesAlgebra k`. This is the category-theoretic form of
`lim 𝒳(S_n)`. -/
def overPowerSeries (k : Type u) [Field k] (𝒳 : GroupoidsOver (specPowerSeries k)) :
    ObjectProperty (FormalObject 𝒳) :=
  fun ξ ↦ ξ.base = powerSeriesAlgebra k

/-- Membership in `overPowerSeries k 𝒳` is equality of the complete local base with
`powerSeriesAlgebra k`. -/
theorem overPowerSeries_iff {k : Type u} [Field k]
    {𝒳 : GroupoidsOver (specPowerSeries k)} (ξ : FormalObject 𝒳) :
    overPowerSeries k 𝒳 ξ ↔ ξ.base = powerSeriesAlgebra k :=
  sorry

/-- The complete local object of `homStack X Z` associated to a fibre object over
`𝟙 (specPowerSeries k)`. -/
def completeLocalOfFiber {k : Type u} [Field k] {X : Over (specPowerSeries k)}
    {Z : GroupoidsOver (specPowerSeries k)}
    (ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    CompleteLocalObject (homStack X Z) :=
  CompleteLocalObject.of (powerSeriesAlgebra k) (fiberInclusion.obj ξ)
    ξ.property

/-- The underlying object of `completeLocalOfFiber ξ` is the fibre inclusion of
`ξ`. -/
theorem completeLocalOfFiber_object {k : Type u} [Field k]
    {X : Over (specPowerSeries k)} {Z : GroupoidsOver (specPowerSeries k)}
    (ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    (completeLocalOfFiber ξ).object = fiberInclusion.obj ξ :=
  sorry

/-- The complete local algebra of `completeLocalOfFiber ξ` is
`powerSeriesAlgebra k`. -/
theorem completeLocalOfFiber_base {k : Type u} [Field k]
    {X : Over (specPowerSeries k)} {Z : GroupoidsOver (specPowerSeries k)}
    (ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    (completeLocalOfFiber ξ).base = powerSeriesAlgebra k :=
  sorry

/-- A fibre morphism over `𝟙 (specPowerSeries k)` is a morphism of the associated
complete local objects. -/
def completeLocalOfFiber_map {k : Type u} [Field k] {X : Over (specPowerSeries k)}
    {Z : GroupoidsOver (specPowerSeries k)}
    {ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))}
    {ξ' : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))} (f : ξ ⟶ ξ') :
    completeLocalOfFiber ξ ⟶ completeLocalOfFiber ξ' :=
  fiberInclusion.map f

/-- `completeLocalOfFiber_map` is fibre inclusion on morphisms. -/
theorem completeLocalOfFiber_map_eq {k : Type u} [Field k]
    {X : Over (specPowerSeries k)} {Z : GroupoidsOver (specPowerSeries k)}
    {ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))}
    {ξ' : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))} (f : ξ ⟶ ξ') :
    completeLocalOfFiber_map f = fiberInclusion.map f :=
  sorry

/-- Restriction of `completeLocalOfFiber ξ` is a formal object over
`powerSeriesAlgebra k`. -/
theorem completeLocalOfFiber_restriction_mem {k : Type u} [Field k]
    {X : Over (specPowerSeries k)} {Z : GroupoidsOver (specPowerSeries k)}
    (ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    overPowerSeries k (homStack X Z) (FormalObject.restriction (completeLocalOfFiber ξ)) :=
  sorry

/-- The canonical restriction `𝒳(S) ⥤ lim 𝒳(S_n)`, sending a fibre object of
`homStack X Z` over `𝟙 (specPowerSeries k)` to the formal object of its
truncations along `Spec(k⟦t⟧ ⧸ m^{n+1}) ⟶ Spec(k⟦t⟧)`. -/
def canonicalRestriction {k : Type u} [Field k] (X : Over (specPowerSeries k))
    (Z : GroupoidsOver (specPowerSeries k)) :
    ((homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) ⥤
      (overPowerSeries k (homStack X Z)).FullSubcategory :=
  (overPowerSeries k (homStack X Z)).lift
    { obj ξ := FormalObject.restriction (completeLocalOfFiber ξ)
      map f := FormalObject.approximation.map (completeLocalOfFiber_map f)
      map_id := sorry
      map_comp := sorry }
    completeLocalOfFiber_restriction_mem

/-- The underlying formal object of `canonicalRestriction` is truncation
restriction of `completeLocalOfFiber`. -/
theorem canonicalRestriction_obj {k : Type u} [Field k]
    (X : Over (specPowerSeries k)) (Z : GroupoidsOver (specPowerSeries k))
    (ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    ((canonicalRestriction X Z).obj ξ).obj =
      FormalObject.restriction (completeLocalOfFiber ξ) :=
  sorry

/-- The complete local algebra of a restricted fibre object is
`powerSeriesAlgebra k`. -/
theorem canonicalRestriction_obj_base {k : Type u} [Field k]
    (X : Over (specPowerSeries k)) (Z : GroupoidsOver (specPowerSeries k))
    (ξ : (homStack X Z).p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    ((canonicalRestriction X Z).obj ξ).obj.base = powerSeriesAlgebra k :=
  sorry

/-- Lemma 110.72.4: in the setup of Stacks 110.72, the canonical restriction
`canonicalRestriction X (classifyingTorsors (constantAbelianScheme A0))` from the
fibre `𝒳(S)` of `homStack X (classifyingTorsors (constantAbelianScheme A0))` over
`S = specPowerSeries k` to formal objects over `powerSeriesAlgebra k` is not
essentially surjective. -/
@[stacks 0AFB]
theorem not_essSurj_canonicalRestriction {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)) :
    ¬ (canonicalRestriction X (classifyingTorsors (constantAbelianScheme A0))).EssSurj :=
  sorry

end AlgebraicGeometry.HomStack
