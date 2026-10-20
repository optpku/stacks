module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OverField.Monomorphism
import StacksCheckRecall

/-!
# Locally quasi-finite algebraic spaces closed under monomorphisms over a field

A monomorphism of algebraic spaces over a field preserves the Stacks property of
being locally quasi-finite over that field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.10.9: Let `k` be a field. Let `f : X ⟶ Y` be a monomorphism of
algebraic spaces over `k`. If `Y` is locally quasi-finite over `k` so is `X`.

Stacks locally quasi-finite over `k` means both locally of finite type and
locally quasi-finite for the canonical structure morphism. -/
@[stacks 06S1]
#check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_over_field_of_mono :
  ∀ {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : X ⟶ Y) [Mono f]
    [LocallyOfFiniteType (SchemeRealization.toBase Y)]
    [LocallyQuasiFinite (SchemeRealization.toBase Y)],
    LocallyOfFiniteType (SchemeRealization.toBase X) ∧
      LocallyQuasiFinite (SchemeRealization.toBase X))
