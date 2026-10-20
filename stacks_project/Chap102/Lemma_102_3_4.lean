module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
import StacksCheckRecall

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

/- Lemma 102.3.4: Let `p : 𝒳 ⟶ 𝒴` and `q : 𝒴 ⟶ 𝒵` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. If `p` and `q` are limit
preserving, then so is the composition `q ∘ p`, written `p ≫ q`. -/
@[stacks 0CMU]
#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Y ⟶ Z)
    [AlgebraicGeometry.Groupoids.Hom.LimitPreserving p]
    [AlgebraicGeometry.Groupoids.Hom.LimitPreserving q],
    AlgebraicGeometry.Groupoids.Hom.LimitPreserving (p ≫ q))
