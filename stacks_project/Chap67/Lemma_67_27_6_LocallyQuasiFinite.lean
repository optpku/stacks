/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality

/-!
# Pointwise quasi-finiteness and locality predicates for algebraic spaces

The pointwise predicate records weak local quasi-finiteness without requiring
local finite type. The locality predicates require both properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.QuasiFiniteAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    QuasiFiniteAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyQuasiFinite (i ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.baseChangeOnSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.baseChangeOnAffineSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.existsSurjectiveEtaleSource :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.forallEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.existsEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.existsZariskiCover.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

end AlgebraicGeometry.AlgebraicSpace
