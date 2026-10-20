/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Dense open restrictions of birational morphisms of algebraic spaces

A birational morphism of decent algebraic spaces with finitely many
irreducible components restricts to an isomorphism between dense opens under
finite type or finite presentation hypotheses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components restricts to an isomorphism between dense opens if it
is locally of finite type with reduced target, or locally of finite presentation. -/
@[stacks 0BBE]
theorem exists_dense_opens_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f]
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (φ : U.X ⟶ V.X),
      Dense U.pointsSet ∧ Dense V.pointsSet ∧
        φ ≫ V.ι = U.ι ≫ f ∧ IsIso φ :=
  sorry

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components that is locally of finite type onto a reduced target
restricts to an isomorphism between dense opens. -/
theorem exists_dense_opens_isIso_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFiniteType f] [IsReduced Y] :
    ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (φ : U.X ⟶ V.X),
      Dense U.pointsSet ∧ Dense V.pointsSet ∧
        φ ≫ V.ι = U.ι ≫ f ∧ IsIso φ :=
  exists_dense_opens_isIso f (Or.inl ⟨inferInstance, inferInstance⟩)

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components that is locally of finite presentation restricts to
an isomorphism between dense opens. -/
theorem exists_dense_opens_isIso_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFinitePresentation f] :
    ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (φ : U.X ⟶ V.X),
      Dense U.pointsSet ∧ Dense V.pointsSet ∧
        φ ≫ V.ι = U.ι ≫ f ∧ IsIso φ :=
  exists_dense_opens_isIso f (Or.inr inferInstance)

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components is an isomorphism over a dense open of its target if it
is quasi-compact or separated and satisfies either of the following conditions:
it is locally of finite type with reduced target, or it is locally of finite
presentation. The restriction is the canonical pullback projection to the
target open subspace. -/
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
  exists_dense_open_isIso_restrict f (Or.inl inferInstance) h

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
  exists_dense_open_isIso_restrict f (Or.inr inferInstance) h

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
  exists_dense_open_isIso_restrict f hqc_or_sep (Or.inl ⟨inferInstance, inferInstance⟩)

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
  exists_dense_open_isIso_restrict f hqc_or_sep (Or.inr inferInstance)

end AlgebraicGeometry.AlgebraicSpace.IsBirational
