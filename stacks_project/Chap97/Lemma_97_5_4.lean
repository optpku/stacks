module

public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap100.Definition_100_9_1_Immersion

/-!
# Open immersions are limit preserving on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and an open immersion is limit preserving
on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreservingOnObjects

/-- Lemma 97.5.4: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. Assume `p` is representable by algebraic spaces
and an open immersion. Then `p` is limit preserving on objects. -/
@[stacks 06CY]
instance of_openImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [OpenImmersion p] : LimitPreservingOnObjects p :=
  sorry

end LimitPreservingOnObjects

end AlgebraicGeometry.Groupoids.Hom
