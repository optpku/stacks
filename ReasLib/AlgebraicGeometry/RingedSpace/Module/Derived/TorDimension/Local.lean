module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local finite Tor dimension on ringed spaces

This file owns local finite Tor dimension for ringed spaces through the canonical derived
restriction functor and topological open covers.  Comparison with the site-local notion belongs
in a separate bridge leaf and is not part of the source-facing predicate.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- A derived `𝒪_X`-module has finite Tor dimension on `U` when its canonical restriction
to the open subspace `U` has finite Tor dimension. -/
abbrev HasFiniteTorDimensionOnOpen
    (E : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  HasFiniteTorDimension (X := X.restrict U.isOpenEmbedding)
    ((moduleRestrictionToOpenDerived X U).obj E)

/-- Definition 20.48.1 (3), object-property owner: derived modules whose restrictions have finite
Tor dimension on the members of an open cover. -/
@[stacks 08CG "(3) object property"]
def locallyFiniteTorDimension : ObjectProperty (ModuleDerived X) :=
  fun E ↦ ∃ (I : Type u) (U : I → Opens X.carrier),
    IsOpenCover U ∧ ∀ i : I, HasFiniteTorDimensionOnOpen E (U i)

/-- Definition 20.48.1 (3): a derived `𝒪_X`-module locally has finite Tor dimension when
it belongs to `locallyFiniteTorDimension`. -/
@[stacks 08CG "(3)"]
abbrev LocallyHasFiniteTorDimension (E : ModuleDerived X) : Prop :=
  locallyFiniteTorDimension (X := X) E

/-- An open cover with finite-Tor-dimension restrictions exhibits local finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_isOpenCover
    {I : Type v} {U : I → Opens X.carrier} {E : ModuleDerived X}
    (hU : IsOpenCover U)
    (hE : ∀ i : I, HasFiniteTorDimensionOnOpen E (U i)) :
    LocallyHasFiniteTorDimension E := sorry

/-- Local finite Tor dimension unfolds to the indexed-open-cover criterion. -/
theorem locallyHasFiniteTorDimension_iff_exists_openCover (E : ModuleDerived X) :
    LocallyHasFiniteTorDimension E ↔
      ∃ (I : Type u) (U : I → Opens X.carrier),
        IsOpenCover U ∧ ∀ i : I, HasFiniteTorDimensionOnOpen E (U i) := sorry

/-- A locally finite-Tor-dimension object admits an open cover with finite-Tor-dimension
restrictions. -/
theorem LocallyHasFiniteTorDimension.exists_openCover
    {E : ModuleDerived X} (hE : LocallyHasFiniteTorDimension E) :
    ∃ (I : Type u) (U : I → Opens X.carrier),
      IsOpenCover U ∧ ∀ i : I, HasFiniteTorDimensionOnOpen E (U i) := sorry

/-- Eliminate local finite Tor dimension through any property implied by all its witnessing open
covers. -/
theorem LocallyHasFiniteTorDimension.elim
    {E : ModuleDerived X} {P : Prop} (hE : LocallyHasFiniteTorDimension E)
    (h : ∀ {I : Type u} (U : I → Opens X.carrier),
      IsOpenCover U → (∀ i : I, HasFiniteTorDimensionOnOpen E (U i)) → P) :
    P := sorry

/-- Local finite Tor dimension is invariant under isomorphism of derived modules. -/
instance locallyFiniteTorDimension_isClosedUnderIsomorphisms :
    (locallyFiniteTorDimension (X := X)).IsClosedUnderIsomorphisms := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
