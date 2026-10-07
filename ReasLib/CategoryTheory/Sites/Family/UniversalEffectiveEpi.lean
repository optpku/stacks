module

public import ReasLib.CategoryTheory.Sites.Family.EffectiveEpi

/-!
# Universally effective epimorphic families

This file records universal effective epimorphy for fixed-target indexed families and its
basic inheritance under base change.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C] {U : C}

/-- A fixed-target family is universally effective epimorphic when its components have
arbitrary pullbacks and every componentwise base change is an effective epimorphic family. -/
class IsUniversalEffectiveEpiFamily (K : Over.{w} U) : Prop where
  /-- Every component of the family admits pullbacks along arbitrary morphisms. -/
  representable (i : K.index) : (𝟭 C).relativelyRepresentable (K.obj i).hom
  /-- Every componentwise base change is an effective epimorphic family. -/
  effectiveEpiFamily {V : C} (f : V ⟶ U)
      [∀ i : K.index, HasPullback (K.obj i).hom f] :
    IsEffectiveEpiFamily (K.baseChange f)

/-- Characterization of universally effective epimorphic families by their components and
all componentwise base changes. -/
theorem isUniversalEffectiveEpiFamily_iff (K : Over.{w} U) :
    IsUniversalEffectiveEpiFamily K ↔
      (∀ i : K.index, (𝟭 C).relativelyRepresentable (K.obj i).hom) ∧
        ∀ {V : C} (f : V ⟶ U) [∀ i : K.index, HasPullback (K.obj i).hom f],
          IsEffectiveEpiFamily (K.baseChange f) := sorry

/-- A universally effective epimorphic family is effective epimorphic over its original
target. -/
theorem IsUniversalEffectiveEpiFamily.toIsEffectiveEpiFamily
    (K : Over.{w} U) [IsUniversalEffectiveEpiFamily K] :
    IsEffectiveEpiFamily K := sorry

/-- Every componentwise base change of a universally effective epimorphic family is again
universally effective epimorphic. -/
theorem IsUniversalEffectiveEpiFamily.baseChange
    (K : Over.{w} U) [IsUniversalEffectiveEpiFamily K]
    {V : C} (f : V ⟶ U) [∀ i : K.index, HasPullback (K.obj i).hom f] :
    IsUniversalEffectiveEpiFamily (K.baseChange f) := sorry

end SemiRepresentableFamily.Over

end CategoryTheory
