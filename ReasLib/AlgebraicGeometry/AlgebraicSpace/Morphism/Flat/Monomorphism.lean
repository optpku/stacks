module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Flat monomorphisms of algebraic spaces

A flat monomorphism of algebraic spaces is representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat monomorphism of algebraic spaces is representable by schemes. -/
theorem relativelyRepresentable_of_flat_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [Mono f] :
    yoneda.relativelyRepresentable f :=
  sorry

/-- The fibre product of a flat monomorphism of algebraic spaces with a morphism
from a scheme is a scheme. -/
@[instance]
theorem isScheme_pullback_of_flat_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [Mono f] {T : Over S} (g : ofOver T ⟶ Y) :
    IsScheme (pullback f g) :=
  sorry

/-- A quasi-compact flat surjective monomorphism of algebraic spaces is an
isomorphism. -/
@[instance]
theorem isIso_of_quasiCompact_flat_surjective_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Flat f] [Surjective f] [Mono f] :
    IsIso f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
