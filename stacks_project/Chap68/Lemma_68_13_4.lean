module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.Field
import StacksCheckRecall

/-!
# Monomorphisms into an fppf Spec(k)-cover

A monomorphism of algebraic spaces into a target that admits a locally finitely
presented, surjective, flat morphism from the spectrum of a field is either
empty or an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.13.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a monomorphism of
algebraic spaces over `S`. Assume there exists a field `k` and a locally
finitely presented, surjective, flat morphism
`g : ofOver (Over.mk σ) ⟶ Y` from `Spec (.of k)`. Then either
`IsEmpty (Points X)` or `IsIso f`. -/
@[stacks 06QY]
#check (AlgebraicGeometry.AlgebraicSpace.isEmpty_or_isIso_of_mono_of_spec_field_fppf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f]
    {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (g : ofOver (Over.mk σ) ⟶ Y)
    [LocallyOfFinitePresentation g] [Surjective g] [Flat g],
    IsEmpty (Points X) ∨ IsIso f)

/- A monomorphism of algebraic spaces over a scheme `S` into a target admitting
a locally finitely presented, surjective, flat morphism from `Spec (.of k)` is
an isomorphism if and only if the source is nonempty. -/
#check (AlgebraicGeometry.AlgebraicSpace.isIso_iff_nonempty_of_mono_of_spec_field_fppf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f]
    {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (g : ofOver (Over.mk σ) ⟶ Y)
    [LocallyOfFinitePresentation g] [Surjective g] [Flat g],
    IsIso f ↔ Nonempty (Points X))

end AlgebraicGeometry.AlgebraicSpace
