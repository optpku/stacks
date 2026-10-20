/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.DenseOpen
import StacksCheckRecall

/-!
# Birational morphisms of algebraic spaces that are isomorphisms over a dense open

A birational morphism of decent algebraic spaces with finitely many irreducible
components becomes an isomorphism after base change to a dense open of the
target, provided it is quasi-compact or separated, and either locally of finite
type with reduced target or locally of finite presentation.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.22.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a birational morphism
of algebraic spaces over `S` which are decent and have finitely many
irreducible components. Assume either `f` is quasi-compact or `f` is separated,
and either `f` is locally of finite type and `Y` is reduced or `f` is locally of
finite presentation. Then there exists a dense open `V ⊂ Y` such that
`f⁻¹(V) ⟶ V` is an isomorphism.

Here `V ⊂ Y` is an `OpenSubspace Y`, dense means `Dense V.pointsSet`, and
`f⁻¹(V) ⟶ V` is `pullback.snd f V.ι`. -/
@[stacks 0BBF] #check (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_dense_open_isIso_restrict :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f]
    (hqc_or_sep : QuasiCompact f ∨ Separated f)
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f),
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι))

/- A quasi-compact birational morphism of decent algebraic spaces with finitely
many irreducible components is an isomorphism over a dense open of the target
when it is locally of finite type onto a reduced space, or locally of finite
presentation. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_dense_open_isIso_restrict_of_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [QuasiCompact f]
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f),
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι))

/- A separated birational morphism of decent algebraic spaces with finitely
many irreducible components is an isomorphism over a dense open of the target
when it is locally of finite type onto a reduced space, or locally of finite
presentation. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_dense_open_isIso_restrict_of_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [Separated f]
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f),
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι))

/- A birational morphism of decent algebraic spaces with finitely many
irreducible components that is locally of finite type onto a reduced target is
an isomorphism over a dense open of the target when it is quasi-compact or
separated. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_dense_open_isIso_restrict_of_locallyOfFiniteType :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFiniteType f] [IsReduced Y]
    (hqc_or_sep : QuasiCompact f ∨ Separated f),
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι))

/- A birational morphism of decent algebraic spaces with finitely many
irreducible components that is locally of finite presentation is an isomorphism
over a dense open of the target when it is quasi-compact or separated. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_dense_open_isIso_restrict_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFinitePresentation f]
    (hqc_or_sep : QuasiCompact f ∨ Separated f),
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι))
