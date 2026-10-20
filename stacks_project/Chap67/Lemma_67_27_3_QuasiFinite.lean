module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite

/-!
# Quasi-finite morphisms of algebraic spaces

A morphism of algebraic spaces is quasi-finite when it is of finite type and
locally quasi-finite. The scheme-level locally quasi-finite predicate does not
include local finite type; the finite-type condition supplies this requirement
and quasi-compactness, matching Stacks Definition 67.27.1 (3).

The shared owner supplies the class and its basic API. This module retains the
source-facing imports and typed checks for existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.quasiFinite_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    QuasiFinite f ↔ FiniteType f ∧ LocallyQuasiFinite f)

#check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, QuasiFinite (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsIso f] → QuasiFinite f)

#check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite.instOfFiniteTypeLocallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [FiniteType f] → [LocallyQuasiFinite f] → QuasiFinite f)

end AlgebraicGeometry.AlgebraicSpace
