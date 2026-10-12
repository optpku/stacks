/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZero

/-!
# Schlessinger's condition (S2) along finite square-zero extensions

The square-zero condition is diagram completion and vertical comparison over
`A ⟶ k ← squareZero Λ k V`. Ordinary (S2) implies this condition for every
finite `k`-module `V`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

variable {F : Type v} [Category.{w} F]

/-- A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies Schlessinger's condition (S2)
along `squareZero Λ k V` if every cospan in `F` lying over `A ⟶ k ← squareZero Λ k V`
completes to a commutative square whose image is a pullback, and any two such
completions `y`, `y'` over the same fibre product admit a fibre morphism
`b : y ⟶ y'` with `b ≫ a' = a`. -/
class HasSchlessingerS2Along (p : F ⥤ ArtinianLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V] : Prop where
  /-- Completions exist for cospans lying over `A ⟶ k ← squareZero Λ k V`. -/
  exists_completion : ∀ {x x0 xV : F} (d : x ⟶ x0) (e : xV ⟶ x0),
    p.IsHomLift (squareZeroToResidue Λ k V) e →
      ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xV),
        CommSq a c d e ∧
          IsPullback (p.map a) (p.map c) (p.map d) (p.map e)
  /-- Two completions over the same square-zero fibre product admit a fibre map identifying
  the legs to the object over `A`. -/
  exists_vertical : ∀ {x x0 xV y y' : F} (d : x ⟶ x0) (e : xV ⟶ x0)
      (a : y ⟶ x) (c : y ⟶ xV) (a' : y' ⟶ x) (c' : y' ⟶ xV),
    p.IsHomLift (squareZeroToResidue Λ k V) e →
      CommSq a c d e →
      CommSq a' c' d e →
      IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
      p.obj y = p.obj y' →
      p.IsHomLift (p.map a) a' →
      p.IsHomLift (p.map c) c' →
        ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a

/-- The identity functor on `ArtinianLocalAlgCat Λ k` satisfies (S2) along every
finite `k`-module. -/
instance instHasSchlessingerS2AlongId (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V] :
    HasSchlessingerS2Along (𝟭 (ArtinianLocalAlgCat Λ k)) V := sorry

/-- Condition (S2) along `squareZero Λ k V` is square-zero diagram completion together with
existence of a fibre morphism identifying the legs to the object over `A`. -/
theorem hasSchlessingerS2Along_spec (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    HasSchlessingerS2Along p V ↔
      (∀ {x x0 xV : F} (d : x ⟶ x0) (e : xV ⟶ x0),
          p.IsHomLift (squareZeroToResidue Λ k V) e →
            ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xV),
              CommSq a c d e ∧
                IsPullback (p.map a) (p.map c) (p.map d) (p.map e)) ∧
        ∀ {x x0 xV y y' : F} (d : x ⟶ x0) (e : xV ⟶ x0)
            (a : y ⟶ x) (c : y ⟶ xV) (a' : y' ⟶ x) (c' : y' ⟶ xV),
          p.IsHomLift (squareZeroToResidue Λ k V) e →
            CommSq a c d e →
            CommSq a' c' d e →
            IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
            p.obj y = p.obj y' →
            p.IsHomLift (p.map a) a' →
            p.IsHomLift (p.map c) c' →
              ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a := sorry

/-- For a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` satisfying (H2), the comparison
map along any pullback of `squareZeroToResidue Λ k V` is bijective. -/
theorem hasSchlessingerH2_squareZero (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [HasSchlessingerH2 F] {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
    (π1 : P ⟶ A) (π2 : P ⟶ squareZero Λ k V)
    (h : IsPullback π1 π2 f (squareZeroToResidue Λ k V)) :
    Function.Bijective
      (pullbackObjMap_subtype F π1 π2 f (squareZeroToResidue Λ k V) h) := sorry

/-- A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfying (S2)
satisfies both clauses of (S2) along `squareZero Λ k V` for every finite `k`-module `V`. -/
instance hasSchlessingerS2Along (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    HasSchlessingerS2Along p V := sorry

end CategoryTheory.Functor
