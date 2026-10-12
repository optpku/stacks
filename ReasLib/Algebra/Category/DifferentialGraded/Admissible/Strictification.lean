/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Admissible
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Strictifying homotopy-commutative squares

An admissibly monic top map permits strictification on the right, and an admissibly epic bottom
map permits the dual strictification on the left.
-/

open CategoryTheory

universe u v w

namespace DifferentialGradedCategory.Comp

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]

namespace IsAdmissibleMono

/-- Lemma 22.27.5 (09QL) (1): the right map of a homotopy-commutative square can be replaced
by a homotopic map when the top map is admissibly monic. -/
@[stacks 09QL]
theorem exists_homotopic_rightMap
    {x y z t : Comp R A} {f : x ⟶ y} {a : x ⟶ z} {b : y ⟶ t} {g : z ⟶ t}
    (hf : IsAdmissibleMono f) (comm : Homotopic x.obj t.obj (f ≫ b) (a ≫ g)) :
    ∃ b' : y ⟶ t, Homotopic y.obj t.obj b b' ∧ CommSq f a b' g := sorry

/-- Homotopy-category form of right strictification. -/
theorem exists_rightMap_inK
    {x y z t : Comp R A} {f : x ⟶ y} {a : x ⟶ z} {b : y ⟶ t} {g : z ⟶ t}
    (hf : IsAdmissibleMono f) (comm : CommSq f.inK a.inK b.inK g.inK) :
    ∃ b' : y ⟶ t, b'.inK = b.inK ∧ CommSq f a b' g := sorry

end IsAdmissibleMono

namespace IsAdmissibleEpi

/-- Lemma 22.27.5 (09QL) (2): the left map of a homotopy-commutative square can be replaced
by a homotopic map when the bottom map is admissibly epic. -/
@[stacks 09QL]
theorem exists_homotopic_leftMap
    {x y z t : Comp R A} {f : x ⟶ y} {a : x ⟶ z} {b : y ⟶ t} {g : z ⟶ t}
    (hg : IsAdmissibleEpi g) (comm : Homotopic x.obj t.obj (f ≫ b) (a ≫ g)) :
    ∃ a' : x ⟶ z, Homotopic x.obj z.obj a a' ∧ CommSq f a' b g := sorry

/-- Homotopy-category form of left strictification. -/
theorem exists_leftMap_inK
    {x y z t : Comp R A} {f : x ⟶ y} {a : x ⟶ z} {b : y ⟶ t} {g : z ⟶ t}
    (hg : IsAdmissibleEpi g) (comm : CommSq f.inK a.inK b.inK g.inK) :
    ∃ a' : x ⟶ z, a'.inK = a.inK ∧ CommSq f a' b g := sorry

end IsAdmissibleEpi

end DifferentialGradedCategory.Comp
