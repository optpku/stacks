module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Unramified monomorphisms of algebraic spaces

Unramified monomorphisms are characterized by universal injectivity, finite type,
and formal unramifiedness. They are representable, separated, and locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a morphism of algebraic spaces, unramified monicity, unramified universal
injectivity, locally finite type monicity, and universally injective locally finite
type formal unramifiedness are equivalent. -/
theorem tfae_unramified_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE [
      Unramified f ∧ Mono f,
      Unramified f ∧ UniversallyInjective f,
      LocallyOfFiniteType f ∧ Mono f,
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f] :=
  sorry

/-- An unramified monomorphism of algebraic spaces is representable. -/
theorem relativelyRepresentable_of_unramified_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [Mono f] : yoneda.relativelyRepresentable f :=
  sorry

/-- An unramified monomorphism of algebraic spaces is locally quasi-finite. -/
instance locallyQuasiFinite_of_unramified_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [Mono f] : LocallyQuasiFinite f :=
  sorry

/-- An unramified monomorphism of algebraic spaces is unramified and universally
injective, and conversely. -/
theorem unramified_mono_iff_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ∧ Mono f ↔ Unramified f ∧ UniversallyInjective f :=
  (tfae_unramified_mono f).out 0 1

/-- An unramified monomorphism of algebraic spaces is locally of finite type and
a monomorphism, and conversely. -/
theorem unramified_mono_iff_locallyOfFiniteType_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ∧ Mono f ↔ LocallyOfFiniteType f ∧ Mono f :=
  (tfae_unramified_mono f).out 0 2

/-- An unramified monomorphism of algebraic spaces is universally injective,
locally of finite type, and formally unramified, and conversely. -/
theorem unramified_mono_iff_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ∧ Mono f ↔
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f :=
  (tfae_unramified_mono f).out 0 3

/-- An unramified morphism of algebraic spaces that is universally injective is
a monomorphism. -/
instance mono_of_unramified_of_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [UniversallyInjective f] : Mono f := by
  have h : (Unramified f ∧ UniversallyInjective f) ↔ (Unramified f ∧ Mono f) :=
    (tfae_unramified_mono f).out 1 0
  exact (h.mp ⟨inferInstance, inferInstance⟩).2

/-- An unramified universally injective morphism of algebraic spaces is separated. -/
instance separated_of_unramified_of_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [UniversallyInjective f] : Separated f :=
  Separated.of_mono f

/-- A locally of finite type monomorphism of algebraic spaces is unramified. -/
instance unramified_of_locallyOfFiniteType_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] : Unramified f := by
  have h : (LocallyOfFiniteType f ∧ Mono f) ↔ (Unramified f ∧ Mono f) :=
    (tfae_unramified_mono f).out 2 0
  exact (h.mp ⟨inferInstance, inferInstance⟩).1

namespace Unramified

/-- An unramified morphism of algebraic spaces is a monomorphism if and only if
it is universally injective. -/
theorem mono_iff_universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] : Mono f ↔ UniversallyInjective f := by
  constructor
  · intro h
    exact ((unramified_mono_iff_universallyInjective f).mp ⟨inferInstance, h⟩).2
  · intro h
    exact ((unramified_mono_iff_universallyInjective f).mpr ⟨inferInstance, h⟩).2

end Unramified

end AlgebraicGeometry.AlgebraicSpace
