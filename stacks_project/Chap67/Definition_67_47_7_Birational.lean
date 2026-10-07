module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import stacks_project.Chap67.Definition_67_47_3_RationalMap
public import stacks_project.Chap67.Definition_67_47_7_Irreducible

/-!
# Birational algebraic spaces

A partial isomorphism of algebraic spaces is an isomorphism of dense open
subspaces over the base. Two algebraic spaces over `S` are birational when
such a partial isomorphism exists.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A partial isomorphism from `X` to `Y` is an isomorphism between dense open
subspaces of `X` and `Y` over `S`. -/
structure PartialIso (X Y : AlgebraicSpace S) where
  /-- The source open subspace of a partial isomorphism. -/
  source : smallZariskiSite X
  /-- The source open subspace is dense in `X`. -/
  dense_source : IsDense source.hom
  /-- The target open subspace of a partial isomorphism. -/
  target : smallZariskiSite Y
  /-- The target open subspace is dense in `Y`. -/
  dense_target : IsDense target.hom
  /-- The underlying isomorphism of open subspaces over `S`. -/
  iso : source.left ≅ target.left

namespace PartialIso

/-- The identity partial isomorphism on `X`, defined on all of `X`. -/
def refl (X : AlgebraicSpace S) : PartialIso X X where
  source := idObj X
  dense_source := isDense_id X
  target := idObj X
  dense_target := isDense_id X
  iso := Iso.refl (idObj X).left

/-- The source of the identity partial isomorphism is the whole space. -/
theorem refl_source (X : AlgebraicSpace S) : (refl X).source = idObj X :=
  sorry

/-- The inverse of a partial isomorphism. -/
def symm {X Y : AlgebraicSpace S} (f : PartialIso X Y) : PartialIso Y X where
  source := f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

/-- The source of the inverse partial isomorphism is the original target open. -/
theorem symm_source {X Y : AlgebraicSpace S} (f : PartialIso X Y) :
    (symm f).source = f.target :=
  sorry

end PartialIso

/-- Algebraic spaces `X` and `Y` over `S` are birational if there exists a partial
isomorphism between them. -/
def Birational (X Y : AlgebraicSpace S) : Prop :=
  Nonempty (PartialIso X Y)

/-- Birationality of algebraic spaces is existence of an isomorphism of dense
open subspaces over `S`. -/
theorem birational_iff {X Y : AlgebraicSpace S} :
    Birational X Y ↔
      ∃ (U : smallZariskiSite X) (V : smallZariskiSite Y) (e : U.left ≅ V.left),
        IsDense U.hom ∧ IsDense V.hom :=
  sorry

namespace Birational

/-- Every algebraic space is birational to itself. -/
theorem refl (X : AlgebraicSpace S) : Birational X X :=
  sorry

/-- Birationality of algebraic spaces is symmetric. -/
theorem symm {X Y : AlgebraicSpace S} (h : Birational X Y) : Birational Y X :=
  sorry

end Birational

/-- On irreducible algebraic spaces, birationality is equivalent to the existence
of isomorphic nonempty open subspaces over `S`. -/
theorem birational_iff_nonempty_open {X Y : AlgebraicSpace S}
    [IsIrreducible X] [IsIrreducible Y] :
    Birational X Y ↔
      ∃ (U : smallZariskiSite X) (V : smallZariskiSite Y) (e : U.left ≅ V.left),
        Nonempty (Points U.left) ∧ Nonempty (Points V.left) :=
  sorry

/-- Representable algebraic spaces over `S` are birational if and only if the
underlying schemes are birational over `S`. -/
theorem birational_ofOver_iff (U V : Over S) :
    Birational (ofOver U) (ofOver V) ↔ Scheme.BirationalOver U.hom V.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
