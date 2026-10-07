module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Fibered.CategoryOver.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Factorization
public import ReasLib.CategoryTheory.Fibered.CategoryOver.InheritedTopology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gerbe morphisms

A morphism `F : X ⟶ Y` of stacks in groupoids exhibits `X` as a gerbe over `Y` when it is
locally essentially surjective on fiber objects and locally lifts fiber morphisms.

## Main declarations

* `CategoryTheory.CartesianBasedFunctor.IsGerbeMorphism` — the neutral universe-polymorphic
  local property.
* `CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism` — its transparent
  groupoid-fibred view.
* `CategoryTheory.StackOver.Groupoids.Hom.IsGerbeMorphism` — its specialization to stack
  morphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Z : StackOver.Groupoids J}

/-- Definition 8.11.4 (tag 06P2): a morphism `F : X ⟶ Y` of stacks in groupoids is a gerbe
over `Y` when its underlying heterogeneous cartesian functor is a gerbe morphism. -/
@[stacks 06P2 "gerbe morphism between stacks in groupoids"]
abbrev StackOver.Groupoids.Hom.IsGerbeMorphism (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsGerbeMorphism J
    (StackOver.Groupoids.Hom.toCartesianBasedFunctor F)

namespace StackOver.Groupoids.Hom.IsGerbeMorphism

/-- A relative gerbe is locally essentially surjective on fiber objects. -/
@[stacks 06P2 "relative-gerbe objectwise readout"]
theorem locallyEssentiallySurjective
    {F : X ⟶ Y} (hF : IsGerbeMorphism F) :
    StackOver.Groupoids.Hom.LocallyEssentiallySurjective F := sorry

/-- A relative gerbe is locally surjective on every canonical Hom-presheaf of its underlying
stack morphism. -/
@[stacks 06P2 "relative-gerbe Hom-presheaf readout"]
theorem homwiseLocallySurjective
    {F : X ⟶ Y} (hF : IsGerbeMorphism F) :
    StackOver.Groupoids.Hom.Homwise.IsLocallySurjective F := sorry

/-- A relative gerbe locally lifts fiber morphisms. -/
@[stacks 06P2 "relative-gerbe local-lifting readout"]
theorem locallyLifts
    {F : X ⟶ Y} (hF : IsGerbeMorphism F) :
    StackOver.Groupoids.Hom.LocallyLifts F := sorry

/-- Lemma 8.11.3: a factorization of a stack morphism, compatible with the original morphism up
to a based natural isomorphism, is a gerbe for the inherited topology exactly when the original
morphism is a relative gerbe. -/
@[stacks 06P1]
theorem iff_factorization
    (F : X ⟶ Y)
    {X' : BasedCategory C}
    (a : X.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Y.toBasedCategory)
    [Functor.IsFibered.InGroupoids F'.toFunctor]
    (ha : a.IsEquivalence)
    (hfactor : Nonempty
      (BasedFunctor.comp a F' ≅ StackOver.Groupoids.Hom.toBasedFunctor F)) :
    IsGerbe (Y.p.inheritedTopology J) F'.toFunctor ↔
      IsGerbeMorphism F := sorry

/-- The strict-equality specialization of `iff_factorization`, retained for consumers whose
factorization triangle commutes definitionally or by a specified equality. -/
@[stacks 06P1 "strict factorization criterion for relative gerbes"]
theorem iff_factorization_of_eq
    (F : X ⟶ Y)
    {X' : BasedCategory C}
    (a : X.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Y.toBasedCategory)
    [Functor.IsFibered.InGroupoids F'.toFunctor]
    (ha : a.IsEquivalence)
    (hfactor : BasedFunctor.comp a F' = StackOver.Groupoids.Hom.toBasedFunctor F) :
    IsGerbe (Y.p.inheritedTopology J) F'.toFunctor ↔
      IsGerbeMorphism F := sorry

/-- Lemma 8.11.3 (tag 06P1), existence form: the relative gerbe condition can be tested on a
factorization through any groupoid-fibered category equivalent to the source.  The intermediate
object and the factorization map are kept as explicit witnesses, so downstream code can reuse the
comparison supplied by `FiberedCategoryOver.Groupoids.Factorization.existsEquivalence` rather than
reconstructing it from a proposition-valued wrapper. -/
@[stacks 06P1 "existence form of the relative-gerbe factorization criterion"]
theorem iff_exists_factorization
    (F : X ⟶ Y) :
    IsGerbeMorphism F ↔
      ∃ (X' : FiberedCategoryOver.Groupoids C)
        (e : X.toGroupoids ≌ X') (F' : X' ⟶ Y.toGroupoids),
        Nonempty
            (e.hom ≫ F' ≅ StackOver.Groupoids.Hom.toGroupoidsMor F) ∧
          IsGerbe (Y.p.inheritedTopology J)
            (FiberedCategoryOver.Groupoids.toFunctor F') := sorry

/-- The relative gerbe condition is exactly the conjunction of local essential surjectivity on
objects and local lifting of fiber morphisms. -/
@[stacks 06P2 "relative-gerbe local criterion"]
theorem iff_localConditions (F : X ⟶ Y) :
    IsGerbeMorphism F ↔
      StackOver.Groupoids.Hom.LocallyEssentiallySurjective F ∧
        StackOver.Groupoids.Hom.LocallyLifts F := sorry

/-- The canonical Hom-presheaf characterization of a relative gerbe: local essential
surjectivity on objects together with homwise local surjectivity. -/
@[stacks 06P2 "relative-gerbe Hom-presheaf criterion"]
theorem iff_homwise (F : X ⟶ Y) :
    IsGerbeMorphism F ↔
      StackOver.Groupoids.Hom.LocallyEssentiallySurjective F ∧
        StackOver.Groupoids.Hom.Homwise.IsLocallySurjective F := sorry

/-- Lemma 8.11.6: relative gerbes of stacks in groupoids are closed under composition. -/
@[stacks 06R3]
theorem comp {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : IsGerbeMorphism F) (hG : IsGerbeMorphism G) :
    IsGerbeMorphism (F ≫ G) := sorry

end StackOver.Groupoids.Hom.IsGerbeMorphism

end CategoryTheory
