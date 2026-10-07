module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.CompactOpen
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.ConnectedComponents

/-!
# Continuity of the Galois action on connected components

This leaf records the direct field-extension form of continuity for the induced Galois action when
the source is compact and the geometric connected components are open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Connected.Continuity

/-- The Galois action on connected components after a separable-closure base change is continuous
when the source is compact and the geometric components are open. -/
theorem continuousSMul_of_compact_open
    {k ksep : Type u} [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    (hopen : ∀ x : FieldExtension.baseChange k ksep f, IsOpen (connectedComponent x)) :
    ContinuousSMul Gal(ksep/k)
      (ConnectedComponents (FieldExtension.baseChange k ksep f)) := sorry

end FieldExtension.Galois.Connected.Continuity

end AlgebraicGeometry
