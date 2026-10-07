module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified

/-!
# Unramified monomorphisms of algebraic spaces

A morphism of algebraic spaces is unramified and a monomorphism if and only if
it is unramified and universally injective, if and only if it is locally of
finite type and a monomorphism, if and only if it is universally injective,
locally of finite type, and formally unramified. In this case it is also
representable, separated, and locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.14.8 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is unramified and
a monomorphism; `f` is unramified and universally injective; `f` is locally of
finite type and a monomorphism; `f` is universally injective, locally of finite
type, and formally unramified. -/
@[stacks 05W6]
theorem tfae_unramified_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE [
      Unramified f ∧ Mono f,
      Unramified f ∧ UniversallyInjective f,
      LocallyOfFiniteType f ∧ Mono f,
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f] :=
  sorry

/-- Lemma 76.14.8 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is unramified and a monomorphism, then `f` is
representable. -/
@[stacks 05W6]
theorem relativelyRepresentable_of_unramified_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [Mono f] : yoneda.relativelyRepresentable f :=
  sorry

/-- Lemma 76.14.8 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is unramified and universally injective, then
`f` is separated. -/
@[stacks 05W6]
instance separated_of_unramified_of_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [UniversallyInjective f] : Separated f :=
  sorry

/-- Lemma 76.14.8 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is unramified and a monomorphism, then `f` is
locally quasi-finite. -/
@[stacks 05W6]
instance locallyQuasiFinite_of_unramified_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [Mono f] : LocallyQuasiFinite f :=
  sorry

/-- An unramified monomorphism of algebraic spaces is unramified and universally
injective, and conversely. -/
theorem unramified_mono_iff_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ∧ Mono f ↔ Unramified f ∧ UniversallyInjective f :=
  sorry

/-- An unramified monomorphism of algebraic spaces is locally of finite type and
a monomorphism, and conversely. -/
theorem unramified_mono_iff_locallyOfFiniteType_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ∧ Mono f ↔ LocallyOfFiniteType f ∧ Mono f :=
  sorry

/-- An unramified monomorphism of algebraic spaces is universally injective,
locally of finite type, and formally unramified, and conversely. -/
theorem unramified_mono_iff_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ∧ Mono f ↔
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f :=
  sorry

/-- An unramified morphism of algebraic spaces that is universally injective is
a monomorphism. -/
instance mono_of_unramified_of_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [UniversallyInjective f] : Mono f :=
  sorry

/-- A locally of finite type monomorphism of algebraic spaces is unramified. -/
instance unramified_of_locallyOfFiniteType_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] : Unramified f :=
  sorry

namespace Unramified

/-- An unramified morphism of algebraic spaces is a monomorphism if and only if
it is universally injective. -/
theorem mono_iff_universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] : Mono f ↔ UniversallyInjective f :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicSpace
