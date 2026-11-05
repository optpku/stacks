module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Free
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero

/-!
# Free Sheaves of Modules

Source-independent predicates for a sheaf of modules that is isomorphic to a free sheaf, or to
a free sheaf on a finite indexing type.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The standard free sheaf of `𝒪`-modules of rank `n`, with its basis lifted to the coefficient
universe. -/
noncomputable abbrev freeFin (n : ℕ) : SheafOfModules.{w} 𝒪 :=
  free (ULift.{w} (Fin n))

/-- A sheaf of `𝒪`-modules is free when it is isomorphic to
`SheafOfModules.free I` for some index type `I`. -/
@[stacks 03DE "(1)"]
class IsFree (F : SheafOfModules.{w} 𝒪) : Prop where
  exists_iso_free : ∃ I : Type w, Nonempty (F ≅ free I)

/-- A sheaf of `𝒪`-modules is finite free when it is isomorphic to
`SheafOfModules.free I` for a finite index type `I`. -/
@[stacks 03DE "(2)"]
class IsFiniteFree (F : SheafOfModules.{w} 𝒪) : Prop where
  exists_iso_free : ∃ I : Type w, Finite I ∧ Nonempty (F ≅ free I)

/-- A free sheaf is free. -/
instance free_isFree (I : Type w) : IsFree (free I : SheafOfModules.{w} 𝒪) := sorry

/-- A free sheaf on a finite index type is finite free. -/
instance free_isFiniteFree (I : Type w) [Finite I] :
    IsFiniteFree (free I : SheafOfModules.{w} 𝒪) := sorry

/-- A finite free sheaf is free after forgetting the finiteness of its index type. -/
instance isFiniteFree_to_isFree (F : SheafOfModules.{w} 𝒪) [IsFiniteFree F] :
    IsFree F := sorry

/-- The free module-sheaf property is closed under isomorphisms. -/
instance isFree_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFree : ObjectProperty (SheafOfModules.{w} 𝒪)) := sorry

namespace IsFree

/-- Transport freeness from the source of a module-sheaf isomorphism to its target. -/
theorem of_iso {M N : SheafOfModules.{w} 𝒪} (e : M ≅ N) [IsFree M] :
    IsFree N := sorry

/-- Freeness is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {M N : SheafOfModules.{w} 𝒪} (e : M ≅ N) :
    IsFree M ↔ IsFree N := sorry

end IsFree

/-- The finite-free module-sheaf property is closed under isomorphisms. -/
instance isFiniteFree_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFiniteFree : ObjectProperty (SheafOfModules.{w} 𝒪)) := sorry

namespace IsFiniteFree

/-- Transport finite freeness from the source of a module-sheaf isomorphism to its target. -/
theorem of_iso {M N : SheafOfModules.{w} 𝒪} (e : M ≅ N) [IsFiniteFree M] :
    IsFiniteFree N := sorry

/-- Finite freeness is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {M N : SheafOfModules.{w} 𝒪} (e : M ≅ N) :
    IsFiniteFree M ↔ IsFiniteFree N := sorry

end IsFiniteFree

end SheafOfModules
