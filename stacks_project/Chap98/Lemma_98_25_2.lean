/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_25_2_Noetherian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 98.25.2

Restricting along the inclusion `(Noetherian/S)_τ ⟶ (Sch/S)_τ` is an
equivalence between the categories of limit-preserving sheaves on these
two sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.StandardTopology

/-- A set-valued functor on `(Sch/S)_τ` that is a sheaf and preserves directed
limits of affine schemes over `S`. -/
def isLimitPreservingSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    ObjectProperty ((Over S)ᵒᵖ ⥤ Type (u + 1)) :=
  fun F ↦ Presheaf.IsSheaf (τ.overTopology S) F ∧
    PreservesDirectedAffineLimits S F

/-- Unfolding of `isLimitPreservingSheaf` into the sheaf condition and directed
affine-limit preservation. -/
theorem isLimitPreservingSheaf_iff (τ : StandardTopology) (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    isLimitPreservingSheaf τ S F ↔
      Presheaf.IsSheaf (τ.overTopology S) F ∧
        PreservesDirectedAffineLimits S F := sorry

/-- A limit-preserving sheaf on `(Sch/S)_τ` is a sheaf for `τ.overTopology S`. -/
theorem isSheaf_of_isLimitPreservingSheaf {τ : StandardTopology} {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} (h : isLimitPreservingSheaf τ S F) :
    Presheaf.IsSheaf (τ.overTopology S) F := sorry

/-- A limit-preserving sheaf on `(Sch/S)_τ` preserves directed affine limits. -/
theorem preservesDirectedAffineLimits_of_isLimitPreservingSheaf
    {τ : StandardTopology} {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (h : isLimitPreservingSheaf τ S F) :
    PreservesDirectedAffineLimits S F := sorry

/-- A set-valued functor on `(Noetherian/S)_τ` that is a sheaf and preserves
directed limits of affine schemes in that subcategory. -/
def isLimitPreservingSheafOnNoetherian (τ : StandardTopology) (S : Scheme.{u}) :
    ObjectProperty ((locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :=
  fun F ↦ Presheaf.IsSheaf (locallyNoetherianTopology τ S) F ∧
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F

/-- Unfolding of `isLimitPreservingSheafOnNoetherian` into the sheaf condition
and directed affine-limit preservation on the locally Noetherian site. -/
theorem isLimitPreservingSheafOnNoetherian_iff (τ : StandardTopology)
    (S : Scheme.{u}) (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :
    isLimitPreservingSheafOnNoetherian τ S F ↔
      Presheaf.IsSheaf (locallyNoetherianTopology τ S) F ∧
        Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F := sorry

/-- A limit-preserving sheaf on `(Noetherian/S)_τ` is a sheaf for
`locallyNoetherianTopology τ S`. -/
theorem isSheaf_of_isLimitPreservingSheafOnNoetherian {τ : StandardTopology}
    {S : Scheme.{u}} {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (h : isLimitPreservingSheafOnNoetherian τ S F) :
    Presheaf.IsSheaf (locallyNoetherianTopology τ S) F := sorry

/-- A limit-preserving sheaf on `(Noetherian/S)_τ` preserves directed affine
limits internal to that subcategory. -/
theorem preservesDirectedAffineLimits_of_isLimitPreservingSheafOnNoetherian
    {τ : StandardTopology} {S : Scheme.{u}}
    {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (h : isLimitPreservingSheafOnNoetherian τ S F) :
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F := sorry

/-- The category of limit-preserving sheaves on `(Sch/S)_τ`. -/
abbrev LimitPreservingSheaf (τ : StandardTopology) (S : Scheme.{u}) :=
  (isLimitPreservingSheaf τ S).FullSubcategory

/-- `LimitPreservingSheaf τ S` is the full subcategory of limit-preserving
sheaves on `τ.overTopology S`. -/
theorem LimitPreservingSheaf_eq (τ : StandardTopology) (S : Scheme.{u}) :
    LimitPreservingSheaf τ S = (isLimitPreservingSheaf τ S).FullSubcategory := sorry

/-- The category of limit-preserving sheaves on `(Noetherian/S)_τ`. -/
abbrev LimitPreservingSheafOnNoetherian (τ : StandardTopology) (S : Scheme.{u}) :=
  (isLimitPreservingSheafOnNoetherian τ S).FullSubcategory

/-- `LimitPreservingSheafOnNoetherian τ S` is the full subcategory of
limit-preserving sheaves on `locallyNoetherianTopology τ S`. -/
theorem LimitPreservingSheafOnNoetherian_eq (τ : StandardTopology)
    (S : Scheme.{u}) :
    LimitPreservingSheafOnNoetherian τ S =
      (isLimitPreservingSheafOnNoetherian τ S).FullSubcategory := sorry

/-- Restriction along `(locallyNoetherian S).ι` sends limit-preserving sheaves
on `(Sch/S)_τ` to limit-preserving sheaves on `(Noetherian/S)_τ`. -/
theorem restrictLimitPreservingSheaf_obj_mem (τ : StandardTopology)
    (S : Scheme.{u}) (F : LimitPreservingSheaf τ S) :
    isLimitPreservingSheafOnNoetherian τ S ((restrictPresheaf S).obj F.obj) := sorry

/-- Restriction of limit-preserving sheaves along the inclusion
`(Noetherian/S)_τ ⟶ (Sch/S)_τ`. -/
def restrictLimitPreservingSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    LimitPreservingSheaf τ S ⥤ LimitPreservingSheafOnNoetherian τ S :=
  (isLimitPreservingSheafOnNoetherian τ S).lift
    ((isLimitPreservingSheaf τ S).ι ⋙ restrictPresheaf S)
    fun F ↦ restrictLimitPreservingSheaf_obj_mem τ S F

/-- The underlying presheaf of a restricted limit-preserving sheaf is the
restriction of the original presheaf. -/
theorem restrictLimitPreservingSheaf_obj (τ : StandardTopology) (S : Scheme.{u})
    (F : LimitPreservingSheaf τ S) :
    ((restrictLimitPreservingSheaf τ S).obj F).obj =
      (restrictPresheaf S).obj F.obj := sorry

/-- Lemma 98.25.2: restricting along the inclusion
`(locallyNoetherian S).ι : (locallyNoetherian S).FullSubcategory ⥤ Over S`
is an equivalence from `LimitPreservingSheaf τ S` to
`LimitPreservingSheafOnNoetherian τ S`, for `τ` one of Zariski, étale, smooth,
syntomic, or fppf, and `S` locally Noetherian. -/
@[stacks 0GE3]
instance restrictLimitPreservingSheaf_isEquivalence
    (τ : StandardTopology) (S : Scheme.{u}) [IsLocallyNoetherian S] :
    (restrictLimitPreservingSheaf τ S).IsEquivalence := sorry

end AlgebraicGeometry.StandardTopology
