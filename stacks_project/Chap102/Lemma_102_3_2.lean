module

public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving

/-!
# Limit-preserving 1-morphisms are limit preserving on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
limit preserving in the sense of Definition 102.3.1 is limit preserving on
objects in the sense of Section 97.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreserving

/-- Lemma 102.3.2: Let `S` be a scheme. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf`. If `f` is limit
preserving (Definition 102.3.1), then `f` is limit preserving on objects
(Criteria for Representability, Section 97.5). -/
@[stacks 0CMS]
instance toLimitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] :
    LimitPreservingOnObjects f := sorry

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
