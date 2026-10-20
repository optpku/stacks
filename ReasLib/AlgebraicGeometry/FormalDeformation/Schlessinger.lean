/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Schlessinger's conditions

The conditions (S1) and (S2) express diagram completion and comparison of completions
for categories cofibered in groupoids over residue-identified Artinian local algebras.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor satisfies Schlessinger's condition (S1) if it is cofibered in groupoids
and every cospan with surjective second base leg has a commutative completion lying
over a pullback of Artinian local algebras. -/
class HasSchlessingerS1 (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  /-- The projection is cofibered in groupoids. -/
  [isCofiberedInGroupoids : IsFibered.InGroupoids p.op]
  /-- Cospans with a surjective second base leg admit completions over base pullbacks. -/
  exists_completion : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
    Function.Surjective (p.map f2).hom →
      ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
        CommSq π1 π2 f1 f2 ∧
          IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)

/-- The identity functor on Artinian local algebras satisfies (S1). -/
instance instHasSchlessingerS1Id :
    HasSchlessingerS1 (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Condition (S1) is cofiberedness in groupoids together with completion over base
pullbacks for every cospan with a surjective second base leg. -/
theorem hasSchlessingerS1_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasSchlessingerS1 p ↔
      IsFibered.InGroupoids p.op ∧
        ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
          Function.Surjective (p.map f2).hom →
            ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
              CommSq π1 π2 f1 f2 ∧
                IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

/-- A functor satisfies Schlessinger's condition (S2) if it is cofibered in groupoids,
every cospan over `A ⟶ k ← k[ε]` has a commutative completion over a base pullback,
and two completions over the same fibre product admit a vertical morphism identifying
their legs to the object over `A`. -/
class HasSchlessingerS2 (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  /-- The projection is cofibered in groupoids. -/
  [isCofiberedInGroupoids : IsFibered.InGroupoids p.op]
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

/-- The identity functor on Artinian local algebras satisfies (S2). -/
instance instHasSchlessingerS2Id :
    HasSchlessingerS2 (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Condition (S2) is cofiberedness in groupoids, dual-number diagram completion,
and existence of a fibre morphism identifying the legs to the object over `A`. -/
theorem hasSchlessingerS2_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasSchlessingerS2 p ↔
      IsFibered.InGroupoids p.op ∧
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
