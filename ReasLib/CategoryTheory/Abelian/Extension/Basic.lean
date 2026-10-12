/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fixed-Endpoint Extensions

This module provides the source-facing data of a short exact sequence with fixed endpoints.
It is a thin, reusable bridge to ShortComplex.ShortExact, retaining the middle object and
endpoint maps without forcing transports through a subtype of short complexes.
-/

namespace CategoryTheory

universe v u

open Limits

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {A B : C}

/-- Definition 12.6.1: an extension of B by A is a short exact sequence
0 ⟶ A ⟶ E ⟶ B ⟶ 0 with fixed endpoints. -/
@[stacks 010J]
structure Extension (A B : C) where
  /-- The middle object of the extension. -/
  E : C
  /-- The monomorphic map from the left endpoint. -/
  f : A ⟶ E
  /-- The epimorphic map to the right endpoint. -/
  g : E ⟶ B
  /-- The two maps compose to zero. -/
  zero : f ≫ g = 0
  /-- The associated short complex is short exact. -/
  shortExact : (ShortComplex.mk f g zero).ShortExact

namespace Extension

/-- The short complex underlying an extension. -/
abbrev toShortComplex (S : Extension A B) : ShortComplex C :=
  ShortComplex.mk S.f S.g S.zero

/-- A morphism of fixed-endpoint extensions is a morphism of their middle
objects that is the identity on both endpoints. -/
@[ext, stacks 010J]
structure Hom (S T : Extension A B) where
  /-- The morphism between the middle objects. -/
  hom : S.E ⟶ T.E
  /-- Compatibility with the left endpoint map. -/
  comm_f : S.f ≫ hom = T.f
  /-- Compatibility with the right endpoint map. -/
  comm_g : hom ≫ T.g = S.g

/-- The identity morphism of a fixed-endpoint extension. -/
def Hom.id (S : Extension A B) : Hom S S where
  hom := 𝟙 S.E
  comm_f := Category.comp_id S.f
  comm_g := Category.id_comp S.g

/-- Compatibility of composition with the left endpoint map. -/
theorem Hom.comp_comm_f {S T U : Extension A B} (f : Hom S T) (g : Hom T U) :
    S.f ≫ (f.hom ≫ g.hom) = U.f := sorry

/-- Compatibility of composition with the right endpoint map. -/
theorem Hom.comp_comm_g {S T U : Extension A B} (f : Hom S T) (g : Hom T U) :
    (f.hom ≫ g.hom) ≫ U.g = S.g := sorry

/-- Composition of morphisms of fixed-endpoint extensions. -/
def Hom.comp {S T U : Extension A B} (f : Hom S T) (g : Hom T U) : Hom S U where
  hom := f.hom ≫ g.hom
  comm_f := Hom.comp_comm_f f g
  comm_g := Hom.comp_comm_g f g

/-- Composition of extension morphisms is associative. -/
theorem Hom.assoc {S T U V : Extension A B}
    (f : Hom S T) (g : Hom T U) (h : Hom U V) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := sorry

/-- Identity is a left unit for extension morphisms. -/
theorem Hom.id_comp {S T : Extension A B} (f : Hom S T) :
    Hom.comp (Hom.id S) f = f := sorry

/-- Identity is a right unit for extension morphisms. -/
theorem Hom.comp_id {S T : Extension A B} (f : Hom S T) :
    Hom.comp f (Hom.id T) = f := sorry

/-- Fixed-endpoint extensions and their endpoint-preserving morphisms form a
category. -/
instance : Category.{v} (Extension A B) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  assoc := Hom.assoc
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id

/-- The left square of the underlying short-complex morphism commutes. -/
theorem Hom.toShortComplex_comm₁₂ {S T : Extension A B} (f : S ⟶ T) :
    𝟙 A ≫ T.toShortComplex.f = S.toShortComplex.f ≫ f.hom := sorry

/-- The right square of the underlying short-complex morphism commutes. -/
theorem Hom.toShortComplex_comm₂₃ {S T : Extension A B} (f : S ⟶ T) :
    f.hom ≫ T.toShortComplex.g = S.toShortComplex.g ≫ 𝟙 B := sorry

/-- An extension morphism determines the canonical morphism of underlying
short complexes. -/
def Hom.toShortComplex {S T : Extension A B} (f : S ⟶ T) :
    S.toShortComplex ⟶ T.toShortComplex where
  τ₁ := 𝟙 A
  τ₂ := f.hom
  τ₃ := 𝟙 B
  comm₁₂ := f.toShortComplex_comm₁₂
  comm₂₃ := f.toShortComplex_comm₂₃

/-- The underlying-short-complex map preserves identity morphisms. -/
theorem Hom.toShortComplex_id (S : Extension A B) :
    (Hom.id S).toShortComplex = 𝟙 S.toShortComplex := sorry

/-- The underlying-short-complex map preserves composition. -/
theorem Hom.toShortComplex_comp {S T U : Extension A B} (f : S ⟶ T) (g : T ⟶ U) :
    (Hom.comp f g).toShortComplex = f.toShortComplex ≫ g.toShortComplex := sorry

/-- The canonical functor from fixed-endpoint extensions to short complexes. -/
def toShortComplexFunctor : Extension A B ⥤ ShortComplex C where
  obj := toShortComplex
  map := Hom.toShortComplex
  map_id := Hom.toShortComplex_id
  map_comp := Hom.toShortComplex_comp

/-- The underlying-short-complex functor remembers every extension morphism. -/
instance toShortComplexFunctor_faithful : (toShortComplexFunctor (A := A) (B := B)).Faithful where
  map_injective := sorry

/-- An extension can be used as its underlying short complex. -/
instance : CoeOut (Extension A B) (ShortComplex C) where
  coe := toShortComplex

/-- The left map of an extension is a monomorphism. -/
instance (S : Extension A B) : Mono S.f :=
  S.shortExact.mono_f

/-- The right map of an extension is an epimorphism. -/
instance (S : Extension A B) : Epi S.g :=
  S.shortExact.epi_g

end Extension

end

end CategoryTheory
