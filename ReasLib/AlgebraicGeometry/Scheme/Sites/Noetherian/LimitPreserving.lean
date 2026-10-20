module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian

/-!
# Restriction of limit-preserving sheaves to locally Noetherian schemes

The full subcategories of set-valued sheaves preserving directed affine limits
and their restriction functor for the five standard topologies.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.StandardTopology

/-- A set-valued presheaf over `S` is a sheaf for the standard topology and
preserves directed limits of affine schemes over `S`. -/
def isLimitPreservingSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    ObjectProperty ((Over S)ᵒᵖ ⥤ Type (u + 1)) :=
  fun F ↦ Presheaf.IsSheaf (τ.overTopology S) F ∧
    PreservesDirectedAffineLimits S F

/-- A limit-preserving sheaf satisfies the sheaf condition and directed
affine-limit preservation. -/
theorem isLimitPreservingSheaf_iff (τ : StandardTopology) (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    isLimitPreservingSheaf τ S F ↔
      Presheaf.IsSheaf (τ.overTopology S) F ∧
        PreservesDirectedAffineLimits S F := sorry

/-- A limit-preserving sheaf over `S` is a sheaf for `τ.overTopology S`. -/
theorem isSheaf_of_isLimitPreservingSheaf {τ : StandardTopology} {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} (h : isLimitPreservingSheaf τ S F) :
    Presheaf.IsSheaf (τ.overTopology S) F := sorry

/-- A limit-preserving sheaf over `S` preserves directed affine limits. -/
theorem preservesDirectedAffineLimits_of_isLimitPreservingSheaf
    {τ : StandardTopology} {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (h : isLimitPreservingSheaf τ S F) :
    PreservesDirectedAffineLimits S F := sorry

/-- A set-valued presheaf on locally Noetherian schemes over `S` is a sheaf
and preserves directed affine limits in that subcategory. -/
def isLimitPreservingSheafOnNoetherian (τ : StandardTopology) (S : Scheme.{u}) :
    ObjectProperty ((locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :=
  fun F ↦ Presheaf.IsSheaf (locallyNoetherianTopology τ S) F ∧
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F

/-- A limit-preserving sheaf on locally Noetherian schemes satisfies the sheaf
condition and directed affine-limit preservation on the restricted site. -/
theorem isLimitPreservingSheafOnNoetherian_iff (τ : StandardTopology)
    (S : Scheme.{u}) (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :
    isLimitPreservingSheafOnNoetherian τ S F ↔
      Presheaf.IsSheaf (locallyNoetherianTopology τ S) F ∧
        Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F := sorry

/-- A limit-preserving sheaf on locally Noetherian schemes is a sheaf for
`locallyNoetherianTopology τ S`. -/
theorem isSheaf_of_isLimitPreservingSheafOnNoetherian {τ : StandardTopology}
    {S : Scheme.{u}} {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (h : isLimitPreservingSheafOnNoetherian τ S F) :
    Presheaf.IsSheaf (locallyNoetherianTopology τ S) F := sorry

/-- A limit-preserving sheaf on locally Noetherian schemes preserves directed
affine limits internal to that subcategory. -/
theorem preservesDirectedAffineLimits_of_isLimitPreservingSheafOnNoetherian
    {τ : StandardTopology} {S : Scheme.{u}}
    {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (h : isLimitPreservingSheafOnNoetherian τ S F) :
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F := sorry

/-- The category of limit-preserving sheaves on the standard site over `S`. -/
abbrev LimitPreservingSheaf (τ : StandardTopology) (S : Scheme.{u}) :=
  (isLimitPreservingSheaf τ S).FullSubcategory

/-- The category of limit-preserving sheaves on the standard site of locally
Noetherian schemes over `S`. -/
abbrev LimitPreservingSheafOnNoetherian (τ : StandardTopology) (S : Scheme.{u}) :=
  (isLimitPreservingSheafOnNoetherian τ S).FullSubcategory

/-- Restriction along `(locallyNoetherian S).ι` sends limit-preserving sheaves
over `S` to limit-preserving sheaves on locally Noetherian schemes over `S`. -/
theorem restrictLimitPreservingSheaf_obj_mem (τ : StandardTopology)
    (S : Scheme.{u}) (F : LimitPreservingSheaf τ S) :
    isLimitPreservingSheafOnNoetherian τ S ((restrictPresheaf S).obj F.obj) := sorry

/-- Restriction of limit-preserving sheaves along the inclusion of locally
Noetherian schemes over `S` into all schemes over `S`. -/
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

/-- For a locally Noetherian base and any of the five standard topologies,
restriction to locally Noetherian schemes is an equivalence between the
categories of limit-preserving sheaves. -/
instance restrictLimitPreservingSheaf_isEquivalence
    (τ : StandardTopology) (S : Scheme.{u}) [IsLocallyNoetherian S] :
    (restrictLimitPreservingSheaf τ S).IsEquivalence := sorry

end AlgebraicGeometry.StandardTopology
