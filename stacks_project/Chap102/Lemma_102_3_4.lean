/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving

/-!
# Composition of limit-preserving 1-morphisms

The composition of limit-preserving 1-morphisms of categories fibred in
groupoids over `(Sch/S)_fppf` is again limit preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreserving

/-- Lemma 102.3.4: Let `p : 𝒳 ⟶ 𝒴` and `q : 𝒴 ⟶ 𝒵` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. If `p` and `q` are limit
preserving, then so is the composition `q ∘ p`, written `p ≫ q`. -/
@[stacks 0CMU]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) [LimitPreserving p] [LimitPreserving q] :
    LimitPreserving (p ≫ q) := sorry

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
