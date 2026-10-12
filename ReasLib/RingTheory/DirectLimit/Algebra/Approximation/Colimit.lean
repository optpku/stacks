/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimit maps of directed algebra approximations

This leaf names the map between the source and target direct limits induced by
a directed ring-hom approximation.  Its bundled and pointwise computation
laws let consumers use the approximation without rebuilding
`Ring.DirectLimit.map` and its compatibility proof.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- The map between the two direct limits induced by the stagewise maps of an
approximation. -/
@[stacks 00R0 "directed approximation colimit map"]
noncomputable def colimitMap (A : Hom f) :
    Ring.DirectLimit A.source (fun i j h ↦ A.sourceMap i j h) →+*
      Ring.DirectLimit A.target (fun i j h ↦ A.targetMap i j h) :=
  Ring.DirectLimit.map A.map (fun _ _ h ↦ A.map_comm h)

/-- The induced colimit map restricts on each source stage to the stagewise
map followed by the corresponding target-stage inclusion. -/
@[stacks 00R0 "directed approximation colimit map"]
theorem colimitMap_comp_of (A : Hom f) (i : A.index) :
    A.colimitMap.comp
        (Ring.DirectLimit.of A.source
          (fun i j h ↦ A.sourceMap i j h) i) =
      (Ring.DirectLimit.of A.target
        (fun i j h ↦ A.targetMap i j h) i).comp (A.map i) := sorry

/-- The induced colimit map sends a source-stage generator to the target-stage
generator determined by the stagewise map. -/
@[simp, stacks 00R0 "directed approximation colimit map"]
theorem colimitMap_of (A : Hom f) (i : A.index) (x : A.source i) :
    A.colimitMap
        (Ring.DirectLimit.of A.source
          (fun i j h ↦ A.sourceMap i j h) i x) =
      Ring.DirectLimit.of A.target
        (fun i j h ↦ A.targetMap i j h) i (A.map i x) := sorry

/-- After the chosen colimit identifications, the induced colimit map is the
prescribed limiting ring homomorphism. -/
@[stacks 00R0 "directed approximation colimit map"]
theorem targetColimit_comp_colimitMap (A : Hom f) :
    A.targetColimit.toRingHom.comp A.colimitMap =
      f.comp A.sourceColimit.toRingHom := sorry

/-- The chosen target-colimit equivalence evaluates the induced colimit map
through the prescribed limiting ring homomorphism. -/
@[simp, stacks 00R0 "directed approximation colimit map"]
theorem targetColimit_colimitMap (A : Hom f)
    (x : Ring.DirectLimit A.source (fun i j h ↦ A.sourceMap i j h)) :
    A.targetColimit (A.colimitMap x) = f (A.sourceColimit x) := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
