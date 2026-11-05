module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Locally Free Sheaves of Modules

This file adds the finite refinement of Mathlib's `SheafOfModules.IsLocallyFree`. The owner is
formulated for modules over an arbitrary sheaf of rings; commutativity and restriction to slice
sites belong to downstream geometric APIs.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of modules is finite locally free when it has local-free data whose local bases
are finite. -/
@[stacks 03DL "(2)", stacks 01C6 "(2)"]
class IsFiniteLocallyFree (M : SheafOfModules.{w} R) : Prop where
  /-- A common local-generator witness for local freeness and finite generation. -/
  exists_data :
    ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧ q.IsFiniteType

/-- Finite local freeness is closed under isomorphisms. -/
instance isFiniteLocallyFree_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFiniteLocallyFree : ObjectProperty (SheafOfModules.{w} R)) := sorry

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The defining local-generator specification of finite local freeness. -/
@[stacks 03DL "local-generator specification", stacks 01C6 "(2), specification"]
theorem isFiniteLocallyFree_iff (M : SheafOfModules.{w} R) :
    IsFiniteLocallyFree M ↔
      ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧ q.IsFiniteType := sorry

namespace IsFiniteLocallyFree

/-- Finite local freeness forgets to Mathlib local freeness. -/
instance toIsLocallyFree
    (M : SheafOfModules.{w} R) [IsFiniteLocallyFree M] : M.IsLocallyFree := sorry

/-- Finite local freeness forgets to Mathlib finite type. -/
instance toIsFiniteType
    (M : SheafOfModules.{w} R) [IsFiniteLocallyFree M] : M.IsFiniteType := sorry

/-- Finite locally free module sheaves are finitely presented. -/
@[stacks 03DL "finite presentation", instance]
instance isFinitePresentation
    (M : SheafOfModules.{w} R) [IsFiniteLocallyFree M] :
    M.IsFinitePresentation := sorry

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Transport finite local freeness from the source of an isomorphism to its target. -/
@[stacks 03DL "invariance under isomorphism"]
theorem of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N)
    [IsFiniteLocallyFree M] :
    IsFiniteLocallyFree N := sorry

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Finite local freeness is invariant under isomorphism. -/
theorem iff_of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) :
    IsFiniteLocallyFree M ↔ IsFiniteLocallyFree N := sorry

end IsFiniteLocallyFree

/-- A free sheaf is locally free. -/
instance free_isLocallyFree (I : Type w) :
    (SheafOfModules.free (R := R) I : SheafOfModules.{w} R).IsLocallyFree := sorry

/-- A free sheaf on a finite indexing type is finite locally free. -/
instance free_isFiniteLocallyFree (I : Type w) [Finite I] :
    IsFiniteLocallyFree (SheafOfModules.free (R := R) I : SheafOfModules.{w} R) := sorry

end SheafOfModules
