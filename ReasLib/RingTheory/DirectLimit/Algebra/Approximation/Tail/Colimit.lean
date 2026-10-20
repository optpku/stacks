module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimit maps of cofinal-tail approximations

This leaf records the naturality square relating the map induced by a tail
approximation to the map induced by the full approximation.  Both bundled and
pointwise forms are exposed so downstream code need not unfold either
`Hom.tail` or `Ring.DirectLimit.map`.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- The source colimit identification of a tail approximation is obtained by
composing the canonical tail/full equivalence with the original source
identification. -/
@[simp, stacks 00R1 "directed approximation tail colimit"]
theorem tail_sourceColimit (A : Hom f) (i₀ : A.index) :
    (A.tail i₀).sourceColimit =
      Ring.DirectLimit.Tail.equivTo
        (fun i j h ↦ A.sourceMap i j h) i₀ A.sourceColimit := sorry

/-- The target colimit identification of a tail approximation is obtained by
composing the canonical tail/full equivalence with the original target
identification. -/
@[simp, stacks 00R1 "directed approximation tail colimit"]
theorem tail_targetColimit (A : Hom f) (i₀ : A.index) :
    (A.tail i₀).targetColimit =
      Ring.DirectLimit.Tail.equivTo
        (fun i j h ↦ A.targetMap i j h) i₀ A.targetColimit := sorry

/-- The colimit map induced by a tail approximation commutes with the
canonical maps from the tail direct limits to the full direct limits. -/
@[stacks 00R1 "directed approximation tail colimit map"]
theorem tail_colimitMap_naturality (A : Hom f) (i₀ : A.index) :
    (Ring.DirectLimit.Tail.toFull
        (fun i j h ↦ A.targetMap i j h) i₀).comp
        ((A.tail i₀).colimitMap) =
      A.colimitMap.comp
        (Ring.DirectLimit.Tail.toFull
          (fun i j h ↦ A.sourceMap i j h) i₀) := sorry

/-- Pointwise form of the naturality square for the colimit map induced by a
tail approximation. -/
@[simp, stacks 00R1 "directed approximation tail colimit map"]
theorem tail_colimitMap_toFull (A : Hom f) (i₀ : A.index)
    (x : Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A.source j.1)
      (fun j k h ↦ A.sourceMap j.1 k.1 h)) :
    Ring.DirectLimit.Tail.toFull
        (fun i j h ↦ A.targetMap i j h) i₀
        ((A.tail i₀).colimitMap x) =
      A.colimitMap
        (Ring.DirectLimit.Tail.toFull
          (fun i j h ↦ A.sourceMap i j h) i₀ x) := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
