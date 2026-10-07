module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap90.Definition_90_10_1_DualNumber

/-!
# Schlessinger's conditions (S1) and (S2)

A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies (S1) when every cospan in `F`
lying over `A1 ⟶ A ← A2` with `A2 ⟶ A` surjective completes to a commutative square
whose image is a pullback in `ArtinianLocalAlgCat`. Condition (S2) is the same
existence for cospans over `A ⟶ k ← k[ε]`, together with existence of a fibre
morphism between any two such completions identifying the legs to the object over `A`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies Schlessinger's condition (S1)
if every cospan in `F` lying over a cospan in `ArtinianLocalAlgCat Λ k` with surjective
`A2 ⟶ A` completes to a commutative square whose image is a pullback. -/
class HasSchlessingerS1 (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  exists_completion : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
    Function.Surjective (p.map f2).hom →
      ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
        CommSq π1 π2 f1 f2 ∧
          IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)

/-- The identity functor on `ArtinianLocalAlgCat Λ k` satisfies (S1). -/
instance instHasSchlessingerS1Id :
    HasSchlessingerS1 (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Condition (S1) is existence of a commutative completion in `F` whose image square is a
pullback, along every cospan with a surjective second leg. -/
theorem hasSchlessingerS1_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasSchlessingerS1 p ↔
      ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
        Function.Surjective (p.map f2).hom →
          ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
            CommSq π1 π2 f1 f2 ∧
              IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

/-- A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies Schlessinger's condition (S2)
if every cospan in `F` lying over `A ⟶ k ← k[ε]` completes to a commutative square whose
image is a pullback, and any two such completions `y`, `y'` over the same fibre product
admit a fibre morphism `b : y ⟶ y'` with `b ≫ a' = a`. -/
class HasSchlessingerS2 (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  /-- Completions exist for cospans lying over `A ⟶ k ← k[ε]`. -/
  exists_completion : ∀ {x x0 xε : F} (d : x ⟶ x0) (e : xε ⟶ x0),
    p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
      ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xε),
        CommSq a c d e ∧
          IsPullback (p.map a) (p.map c) (p.map d) (p.map e)
  /-- Two completions over the same dual-number fibre product admit a fibre map identifying
  the legs to the object over `A`. -/
  exists_vertical : ∀ {x x0 xε y y' : F} (d : x ⟶ x0) (e : xε ⟶ x0)
      (a : y ⟶ x) (c : y ⟶ xε) (a' : y' ⟶ x) (c' : y' ⟶ xε),
    p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
      CommSq a c d e →
      CommSq a' c' d e →
      IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
      p.obj y = p.obj y' →
      p.IsHomLift (p.map a) a' →
      p.IsHomLift (p.map c) c' →
        ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a

/-- The identity functor on `ArtinianLocalAlgCat Λ k` satisfies (S2). -/
instance instHasSchlessingerS2Id :
    HasSchlessingerS2 (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Condition (S2) is dual-number diagram completion together with existence of a fibre
morphism identifying the legs to the object over `A`. -/
theorem hasSchlessingerS2_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasSchlessingerS2 p ↔
      (∀ {x x0 xε : F} (d : x ⟶ x0) (e : xε ⟶ x0),
          p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
            ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xε),
              CommSq a c d e ∧
                IsPullback (p.map a) (p.map c) (p.map d) (p.map e)) ∧
        ∀ {x x0 xε y y' : F} (d : x ⟶ x0) (e : xε ⟶ x0)
            (a : y ⟶ x) (c : y ⟶ xε) (a' : y' ⟶ x) (c' : y' ⟶ xε),
          p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
            CommSq a c d e →
            CommSq a' c' d e →
            IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
            p.obj y = p.obj y' →
            p.IsHomLift (p.map a) a' →
            p.IsHomLift (p.map c) c' →
              ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a := sorry

end CategoryTheory.Functor
