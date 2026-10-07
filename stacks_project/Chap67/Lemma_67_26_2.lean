module

public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Normal.Nagata.Dedekind
public import stacks_project.Chap67.Lemma_67_26_1

/-!
# Ubiquity of Nagata algebraic spaces

Algebraic spaces locally of finite type over a Nagata scheme, a field, a Noetherian
complete local ring, `ℤ`, or a Dedekind ring of characteristic zero are Nagata.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 67.26.2 (1): Any algebraic space locally of finite type over a Nagata scheme is
Nagata. -/
@[stacks 0BAV]
theorem isNagata_scheme {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    [Scheme.Nagata T.left] (f : X ⟶ ofOver T) [LocallyOfFiniteType f] :
    IsNagata X := sorry

/-- Lemma 67.26.2 (2): Any algebraic space locally of finite type over a field is Nagata. -/
@[stacks 0BAV]
theorem isNagata_field {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f] : IsNagata X := sorry

/-- Lemma 67.26.2 (3): Any algebraic space locally of finite type over a Noetherian complete
local ring is Nagata. -/
@[stacks 0BAV]
theorem isNagata_completeLocal {S : Scheme.{u}} {X : AlgebraicSpace S} {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (σ : Spec (CommRingCat.of R) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f] : IsNagata X := sorry

/-- Lemma 67.26.2 (4): Any algebraic space locally of finite type over `ℤ` is Nagata. -/
@[stacks 0BAV]
theorem isNagata_int {S : Scheme} {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of ℤ) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f] : IsNagata X := sorry

/-- Lemma 67.26.2 (5): Any algebraic space locally of finite type over a Dedekind ring of
characteristic zero is Nagata. -/
@[stacks 0BAV]
theorem isNagata_dedekind {S : Scheme.{u}} {X : AlgebraicSpace S} {R : Type u}
    [CommRing R] [IsDedekindDomain R] [CharZero R]
    (σ : Spec (CommRingCat.of R) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f] : IsNagata X := sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
