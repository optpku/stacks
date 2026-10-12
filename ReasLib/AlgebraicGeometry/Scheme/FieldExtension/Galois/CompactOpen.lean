/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.KrullTopology
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.CompactOpen
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic

/-!
# Compact-open descent along a Galois field extension

This leaf records the finite-subextension and open-subgroup consequences for compact opens of a
field-extension base change.  It uses the direct-morphism field-extension API and does not depend
on any Stacks chapter wrapper.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.CompactOpen

/-- A compact open after a Galois field extension descends to a finite intermediate field. -/
theorem exists_finiteSubextension_preimage_eq
    {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (V : CompactOpens (FieldExtension.baseChange k kbar f).carrier) :
    ∃ K' : IntermediateField k kbar, FiniteDimensional k K' ∧
      ∃ V' : CompactOpens (FieldExtension.baseChange k K' f).carrier,
        (Opens.map (Scheme.AffineBaseChange.Subalgebra.map f K'.toSubalgebra).base).obj V'.toOpens =
          V.toOpens := sorry

/-- A compact open after a Galois field extension has an open Galois stabilizer. -/
theorem exists_openSubgroup_stabilizing
    {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (V : CompactOpens (FieldExtension.baseChange k kbar f).carrier) :
    ∃ H : OpenSubgroup Gal(kbar/k),
      ∀ σ : H,
        (Opens.map (FieldExtension.Galois.map k kbar f σ.1).base).obj V.toOpens =
          V.toOpens := sorry

end FieldExtension.Galois.CompactOpen

end AlgebraicGeometry
