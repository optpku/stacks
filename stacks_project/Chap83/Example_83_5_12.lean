module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap83.Example_83_5_12_Relation
public import stacks_project.Chap83.Example_83_5_12_Spaces

/-!
# Morphisms that agree on field-valued points but fail to be invariant

The involution quotient sheaf `X` of Spaces, Example 65.14.1, together with
`Y = Spec (PowerSeries k)`, supplies reduced quasi-separated algebraic spaces
and a pair of morphisms which agree on field-valued points but are unequal.
The resulting `s = 1`, `t = -1` pre-relation is set-theoretically invariant
for `a` but not invariant.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- Example 83.5.12 (1): the morphisms `fromDisk k` and `fromDiskNeg k` from
`Y = Spec (PowerSeries k)` to the involution quotient `X` agree on every
field-valued point of `Y`. -/
@[stacks 048Z]
theorem eq_on_fieldValuedPoints (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] (σ : Spec (.of K) ⟶ base k)
    (p : Over.mk σ ⟶ formalDisk k) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map p ≫ fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map p ≫
        fromDiskNeg k := sorry

/-- Example 83.5.12 (2): the morphisms `fromDisk k` and `fromDiskNeg k` are not
equal as morphisms `Y ⟶ X`. -/
@[stacks 048Z]
theorem fromDisk_ne_fromDiskNeg (k : Type u) [Field k] [NeZero (2 : k)] :
    fromDisk k ≠ fromDiskNeg k := sorry

/-- Example 83.5.12 (3): with `R = U = Y`, `s = 1`, `t = -1` and `φ = fromDisk k`,
every geometric point of `Y` equalizes `s` and `t` after postcomposition with
`fromDisk k`. -/
@[stacks 048Z]
theorem eq_on_geometricPoints (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] [IsAlgClosed K] (σ : Spec (.of K) ⟶ base k)
    (p : Over.mk σ ⟶ formalDisk k) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (p ≫ (involutionPreRelation k).s) ≫ fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (p ≫ (involutionPreRelation k).t) ≫ fromDisk k := sorry

/-- Example 83.5.12 (4): with `R = U = Y`, `s = 1`, `t = -1` and `φ = fromDisk k`,
the sheaf morphisms `t ≫ φ` and `s ≫ φ` are unequal, so local separatedness of
`X` cannot be weakened to quasi-separatedness in Lemma 83.5.11. -/
@[stacks 048Z]
theorem not_t_fromDisk_eq_s_fromDisk (k : Type u) [Field k] [NeZero (2 : k)] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (involutionPreRelation k).t ≫ fromDisk k ≠
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (involutionPreRelation k).s ≫ fromDisk k := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
