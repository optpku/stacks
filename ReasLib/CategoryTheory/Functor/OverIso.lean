/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Equivalence

/-!
# Pseudo-slice morphisms over a base

This module owns functors whose projection triangles commute by an invertible comparison, together
with composition and equivalence computations for those functors.
-/

@[expose] public section

namespace CategoryTheory

/-- A functor equipped with an invertible comparison between its target projection and its source
projection. This is the universe-polymorphic `1`-cell datum of the pseudo-slice of categories over
`D`: unlike `BasedFunctor`, the triangle commutes up to a specified natural isomorphism.

The projections are kept as explicit parameters rather than repackaged as `BasedCategory`
objects, so `A`, `B`, and `D` may live in independent universes and composite projections can be
used directly. `BasedCategory.StrictIso` is a different, stronger notion: it additionally requires a
strict inverse on total categories. -/
structure Functor.OverIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (p : A ⥤ D) (q : B ⥤ D) where
  /-- The functor between total categories. -/
  functor : A ⥤ B
  /-- Compatibility with the two base projections. -/
  iso : functor ⋙ q ≅ p

namespace Functor.OverIso

/-- The identity functor with its canonical unitor comparison over a projection. -/
def id {A D : Type*} [Category A] [Category D] (p : A ⥤ D) : Functor.OverIso p p where
  functor := 𝟭 A
  iso := p.leftUnitor

/-- The underlying functor of the identity over-base morphism is the identity functor. -/
@[simp]
theorem id_functor {A D : Type*} [Category A] [Category D] (p : A ⥤ D) :
    (id p).functor = 𝟭 A := sorry

/-- The base comparison of the identity over-base morphism is the canonical left unitor. -/
@[simp]
theorem id_iso {A D : Type*} [Category A] [Category D] (p : A ⥤ D) :
    (id p).iso = p.leftUnitor := sorry

/-- Regard a strictly commuting projection triangle as a functor commuting up to isomorphism. -/
def ofEq {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : A ⥤ B) (h : F ⋙ q = p) : Functor.OverIso p q where
  functor := F
  iso := eqToIso h

/-- The underlying functor of a strictly commuting over-base morphism is the supplied
functor. -/
@[simp]
theorem ofEq_functor {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : A ⥤ B) (h : F ⋙ q = p) :
    (ofEq F h).functor = F := sorry

/-- The base comparison attached to a strictly commuting triangle is the equality
isomorphism of that triangle. -/
@[simp]
theorem ofEq_iso {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : A ⥤ B) (h : F ⋙ q = p) :
    (ofEq F h).iso = eqToIso h := sorry

/-- Compose two functors carrying invertible base comparisons. Repeated use of `comp` handles
chains of arbitrary length without introducing arity-specific APIs. -/
def comp
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {p : A ⥤ E} {q : B ⥤ E} {r : D ⥤ E}
    (F : Functor.OverIso p q) (G : Functor.OverIso q r) : Functor.OverIso p r where
  functor := F.functor ⋙ G.functor
  iso := Functor.associator F.functor G.functor r ≪≫
    Functor.isoWhiskerLeft F.functor G.iso ≪≫ F.iso

/-- The underlying functor of a composite over-base morphism is the composite of the underlying
functors. -/
@[simp]
theorem comp_functor
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {p : A ⥤ E} {q : B ⥤ E} {r : D ⥤ E}
    (F : Functor.OverIso p q) (G : Functor.OverIso q r) :
    (F.comp G).functor = F.functor ⋙ G.functor := sorry

/-- The base comparison of a composite over-base morphism is obtained by associating,
whiskering the second comparison, and then applying the first comparison. -/
@[simp]
theorem comp_iso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {p : A ⥤ E} {q : B ⥤ E} {r : D ⥤ E}
    (F : Functor.OverIso p q) (G : Functor.OverIso q r) :
    (F.comp G).iso =
      Functor.associator F.functor G.functor r ≪≫
        Functor.isoWhiskerLeft F.functor G.iso ≪≫ F.iso := sorry

/-- Equivalence of the underlying functors is preserved by composition. -/
theorem compFunctorIsEquivalence
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {p : A ⥤ E} {q : B ⥤ E} {r : D ⥤ E}
    (F : Functor.OverIso p q) (G : Functor.OverIso q r)
    [F.functor.IsEquivalence] [G.functor.IsEquivalence] :
    (F.comp G).functor.IsEquivalence := sorry
/- Proof strategy: unfold only `Functor.OverIso.comp` at the underlying-functor projection, then
use the canonical `Functor.IsEquivalence` instance for a composite of equivalences. -/

/-- Bundle an over-base morphism whose underlying functor is an equivalence as the canonical
equivalence of total categories. The base comparison remains owned by the original
`Functor.OverIso`. -/
noncomputable def asEquivalence
    {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : Functor.OverIso p q)
    [F.functor.IsEquivalence] : A ≌ B :=
  F.functor.asEquivalence

/-- The forward functor of the equivalence selected from an over-base morphism is its underlying
functor. -/
@[simp]
theorem asEquivalence_functor
    {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : Functor.OverIso p q)
    [F.functor.IsEquivalence] :
    F.asEquivalence.functor = F.functor := sorry

/-- Reverse an over-base morphism whose underlying functor is an equivalence. The inverse base
comparison is derived canonically from the forward one and the selected quasi-inverse. -/
noncomputable def inverse
    {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : Functor.OverIso p q)
    [F.functor.IsEquivalence] : Functor.OverIso q p where
  functor := F.asEquivalence.inverse
  iso := Iso.inverseCompIso F.iso.symm

/-- The underlying functor of the reversed over-base morphism is the canonical inverse
equivalence functor. -/
@[simp]
theorem inverse_functor
    {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : Functor.OverIso p q)
    [F.functor.IsEquivalence] :
    F.inverse.functor = F.asEquivalence.inverse := sorry

/-- The base comparison of the reversed over-base morphism is the canonical comparison
obtained from the forward comparison and the selected inverse equivalence. -/
@[simp]
theorem inverse_iso
    {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : Functor.OverIso p q)
    [F.functor.IsEquivalence] :
    F.inverse.iso = Iso.inverseCompIso F.iso.symm := sorry

/-- The underlying functor of the reversed over-base morphism is an equivalence. -/
theorem inverseFunctorIsEquivalence
    {A B D : Type*} [Category A] [Category B] [Category D]
    {p : A ⥤ D} {q : B ⥤ D} (F : Functor.OverIso p q)
    [F.functor.IsEquivalence] :
    F.inverse.functor.IsEquivalence := sorry
/- Proof strategy: rewrite with `inverse_functor`; the inverse functor of an equivalence has the
canonical `Functor.IsEquivalence` instance. -/

end Functor.OverIso

end CategoryTheory
