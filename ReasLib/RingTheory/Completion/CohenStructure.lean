module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.RegularLocalRing.Parameters

@[expose] public section

/-!
# Cohen Structures

This module packages the reusable finite regular complete-local source in a
Cohen-structure argument as an algebra map, rather than fixing a chosen
subring of the target.

@stack 032D
-/

universe u v

open IsLocalRing

namespace Algebra

/-- A finite regular complete-local source for an algebra.  The source map is
local, injective, and induces a bijection on residue fields. -/
@[stacks 032D]
class IsCohenStructure (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [IsLocalRing R] [Algebra A R] : Prop where
  /-- The source is a complete local ring. -/
  completeLocal : IsCompleteLocalRing A
  /-- The source is a regular local ring. -/
  regularLocal : IsRegularLocalRing A
  /-- The structure map is local. -/
  localHom : IsLocalHom (algebraMap A R)
  /-- The structure map is injective. -/
  algebraMap_injective : Function.Injective (algebraMap A R)
  /-- The structure map induces a bijection on residue fields. -/
  residueField_bijective :
    Function.Bijective (ResidueField.map (algebraMap A R))
  /-- The target is finite as a module over the source. -/
  moduleFinite : Module.Finite A R

end Algebra

namespace Algebra.IsCohenStructure

/-- A Cohen structure has a local structure map. -/
instance toIsLocalHom
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [h : Algebra.IsCohenStructure A R] :
    IsLocalHom (algebraMap A R) := h.localHom

/-- The target of a Cohen structure is finite over its source. -/
instance toModuleFinite
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [h : Algebra.IsCohenStructure A R] : Module.Finite A R :=
  h.moduleFinite

/-- The defining completeness, regularity, locality, injectivity, residue-field,
and finiteness conditions of a Cohen structure.

The explicit witness fixes the source complete-local structure only in this
statement: the target `R` cannot be inferred from `IsCompleteLocalRing A`, so
that field cannot be exposed as an unambiguous global instance. -/
@[stacks 032D "Cohen structure specification"]
theorem spec
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (h : Algebra.IsCohenStructure A R) :
    letI : IsCompleteLocalRing A := h.completeLocal
    letI : IsLocalHom (algebraMap A R) := h.localHom
    IsCompleteLocalRing A ∧ IsRegularLocalRing A ∧
      IsLocalHom (algebraMap A R) ∧ Function.Injective (algebraMap A R) ∧
        Function.Bijective (ResidueField.map (algebraMap A R)) ∧ Module.Finite A R := sorry

/-- The source of a Cohen structure into a domain is a domain. -/
theorem isDomain
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsDomain R] (h : Algebra.IsCohenStructure A R) :
    IsDomain A := sorry

/-- A Cohen structure is a finite-type algebra. -/
theorem finiteType
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (h : Algebra.IsCohenStructure A R) : Algebra.FiniteType A R := sorry

end Algebra.IsCohenStructure

namespace IsCompleteLocalRing

/-- Lemma 10.160.11, tag `032D`: a Noetherian complete local domain admits a
finite regular complete-local Cohen structure. -/
@[stacks 032D]
theorem exists_cohenStructure
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra A R), Algebra.IsCohenStructure A R := sorry

end IsCompleteLocalRing
