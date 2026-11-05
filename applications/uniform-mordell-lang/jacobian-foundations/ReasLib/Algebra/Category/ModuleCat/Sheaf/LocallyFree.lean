module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for locally free module sheaves

This leaf owns the site-generic closure API for Mathlib's
`SheafOfModules.IsLocallyFree` predicate.  The defining local-generator data remain in Mathlib;
this file only exposes the object-property and isomorphism interfaces used by downstream
comparison arguments.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}}
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The locally free `R`-module-sheaf property is closed under isomorphisms. -/
instance isLocallyFree_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsLocallyFree : ObjectProperty (SheafOfModules.{w} R)) := sorry

namespace IsLocallyFree

/-- Transport local freeness from the source of a module-sheaf isomorphism to its target. -/
theorem of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) [M.IsLocallyFree] :
    N.IsLocallyFree := sorry

/-- Local freeness is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) :
    M.IsLocallyFree ↔ N.IsLocallyFree := sorry

end IsLocallyFree

end SheafOfModules
