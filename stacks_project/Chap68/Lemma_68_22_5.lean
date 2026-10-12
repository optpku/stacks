/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Definition_68_22_1_Birational

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

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/-- Lemma 68.22.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a birational morphism
of algebraic spaces over `S` which are decent and have finitely many
irreducible components. Assume either `f` is quasi-compact or `f` is separated,
and either `f` is locally of finite type and `Y` is reduced or `f` is locally of
finite presentation. Then there exists a dense open `V ⊂ Y` such that
`f⁻¹(V) ⟶ V` is an isomorphism.

Here `V ⊂ Y` is an `OpenSubspace Y`, dense means `Dense V.pointsSet`, and
`f⁻¹(V) ⟶ V` is `pullback.snd f V.ι`. -/
@[stacks 0BBF]
theorem exists_dense_open_isIso_restrict {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f]
    (hqc_or_sep : QuasiCompact f ∨ Separated f)
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι) :=
  sorry

/-- A quasi-compact birational morphism of decent algebraic spaces with finitely
many irreducible components is an isomorphism over a dense open of the target
when it is locally of finite type onto a reduced space, or locally of finite
presentation. -/
theorem exists_dense_open_isIso_restrict_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [QuasiCompact f]
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι) :=
  sorry

/-- A separated birational morphism of decent algebraic spaces with finitely
many irreducible components is an isomorphism over a dense open of the target
when it is locally of finite type onto a reduced space, or locally of finite
presentation. -/
theorem exists_dense_open_isIso_restrict_of_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [Separated f]
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι) :=
  sorry

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components that is locally of finite type onto a reduced target is
an isomorphism over a dense open of the target when it is quasi-compact or
separated. -/
theorem exists_dense_open_isIso_restrict_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFiniteType f] [IsReduced Y]
    (hqc_or_sep : QuasiCompact f ∨ Separated f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι) :=
  sorry

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components that is locally of finite presentation is an isomorphism
over a dense open of the target when it is quasi-compact or separated. -/
theorem exists_dense_open_isIso_restrict_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFinitePresentation f]
    (hqc_or_sep : QuasiCompact f ∨ Separated f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsIso (pullback.snd f V.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBirational
