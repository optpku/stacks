/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.CommAlg
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal tails in `CommAlgCat`

This leaf packages a tail of a directed system of commutative rings as a
diagram of algebras over its base stage.  The categorical colimit statements
are necessarily single-universe: a cocone in `CommAlgCat.{u}` has its vertex
in `Type u`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace CommAlgCat.DirectLimit.Tail

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable {A : I → Type u} [∀ i, CommRing (A i)]

/-- The upper tail above `i0`, regarded as a directed diagram of commutative
algebras over the base stage `A i0`. -/
@[stacks 00QV "commutative-algebra direct-limit tail"]
noncomputable def diagram
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I) :
    Set.Ici i0 ⥤ CommAlgCat.{u} (A i0) where
  obj j :=
    letI : Algebra (A i0) (A j.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
    CommAlgCat.of (A i0) (A j.1)
  map {j k} h :=
    letI : Algebra (A i0) (A j.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 k
    CommAlgCat.ofHom
      (Ring.DirectLimit.Algebra.Tail.transition f i0 (leOfHom h))
  map_id := sorry
  map_comp := sorry

/-- The direct limit of the tail diagram identifies with the original direct
limit as an algebra over the tail base stage. -/
@[stacks 00QV "commutative-algebra direct-limit tail"]
noncomputable def equivToFull
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I) :
    letI : Algebra (A i0)
      (CommAlgCat.DirectLimit.ring (diagram f i0)) :=
        CommAlgCat.DirectLimit.algebra (diagram f i0)
    letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
    CommAlgCat.DirectLimit.ring (diagram f i0) ≃ₐ[A i0]
      Ring.DirectLimit A (fun i j h ↦ f i j h) :=
  letI : Algebra (A i0)
    (CommAlgCat.DirectLimit.ring (diagram f i0)) :=
      CommAlgCat.DirectLimit.algebra (diagram f i0)
  letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
    Ring.DirectLimit.Algebra.stageAlgebra f i0
  { __ := Ring.DirectLimit.Tail.equiv f i0
    commutes' := sorry }

/-- The tail/full algebra equivalence sends the class of a tail-stage element
to the corresponding class in the full direct limit. -/
@[stacks 00QV "commutative-algebra direct-limit tail"]
theorem equivToFull_of
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) (x : A j.1) :
    letI : Algebra (A i0)
      (CommAlgCat.DirectLimit.ring (diagram f i0)) :=
        CommAlgCat.DirectLimit.algebra (diagram f i0)
    letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
    equivToFull f i0
        (Ring.DirectLimit.of (fun k : Set.Ici i0 ↦ A k.1)
          (fun k l h ↦ f k.1 l.1 h) j x) =
      Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1 x := sorry

/-- The full direct limit, with the tail-stage maps, is a cocone over the
tail diagram. -/
@[stacks 00QV "commutative-algebra direct-limit tail"]
noncomputable def fullCocone
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I) :
    Cocone (diagram f i0) :=
  letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
    Ring.DirectLimit.Algebra.stageAlgebra f i0
  { pt := CommAlgCat.of (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h))
    ι :=
      { app := fun j ↦
          letI : Algebra (A i0) (A j.1) :=
            Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
          CommAlgCat.ofHom (Ring.DirectLimit.Algebra.Tail.ofFull f i0 j)
        naturality := sorry } }

/-- The full direct limit is colimiting for its cofinal tail diagram in
`CommAlgCat (A i0)`. -/
@[stacks 00QV "commutative-algebra direct-limit tail"]
noncomputable def fullIsColimit
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I) :
    IsColimit (fullCocone f i0) :=
  letI : Algebra (A i0)
    (CommAlgCat.DirectLimit.ring (diagram f i0)) :=
      CommAlgCat.DirectLimit.algebra (diagram f i0)
  letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
    Ring.DirectLimit.Algebra.stageAlgebra f i0
  let e := equivToFull f i0
  { desc := fun s ↦
      CommAlgCat.ofHom
        ((CommAlgCat.DirectLimit.desc (diagram f i0) s).comp e.symm.toAlgHom)
    fac := sorry
    uniq := sorry }

end CommAlgCat.DirectLimit.Tail
