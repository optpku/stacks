/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Telescope Presentation Data

The intrinsic predicate `HomotopyColimit.IsOf` merely asserts existence. This
leaf retains the explicit coproduct cocone and telescope triangle needed by
downstream constructions, without installing a local `HasCoproduct` instance.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 090Z: an explicit coproduct cocone and distinguished telescope triangle presenting
`X` as a sequential homotopy colimit of `K`. -/
@[stacks 090Z]
structure Presentation (K : ℕ ⥤ D) (X : D) where
  /-- The explicitly chosen coproduct cocone of the terms of `K`. -/
  coproduct : ColimitCocone (Discrete.functor K.obj)
  /-- The morphism from the chosen coproduct to the presented homotopy-colimit object. -/
  toCocone : coproduct.cocone.pt ⟶ X
  /-- The connecting morphism of the telescope triangle. -/
  connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧
  /-- The telescope triangle determined by the stored coproduct and morphisms is distinguished. -/
  distinguished :
    Triangle.mk (CoproductCocone.telescopeMap K coproduct) toCocone connecting ∈ distTriang D

/-- The `n`th inclusion into the explicit coproduct stored by a telescope presentation. -/
def Presentation.coproductInclusion {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (n : ℕ) : K.obj n ⟶ P.coproduct.cocone.pt :=
  CoproductCocone.inclusion P.coproduct n

/-- The canonical map from the `n`th term of a sequential diagram to the object presented as
its homotopy colimit. -/
@[stacks 090Z]
def Presentation.ι {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (n : ℕ) : K.obj n ⟶ X :=
  P.coproductInclusion n ≫ P.toCocone

/-- A presentation leg is the corresponding explicit coproduct inclusion followed by the
stored coproduct-to-cocone map. -/
@[simp, reassoc]
theorem Presentation.ι_eq {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.ι n = P.coproductInclusion n ≫ P.toCocone := sorry

/-- The distinguished telescope triangle encoded by a presentation. -/
@[stacks 090Z]
def Presentation.triangle {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) : Triangle D :=
  Triangle.mk (CoproductCocone.telescopeMap K P.coproduct) P.toCocone P.connecting

/-- The first morphism of a presentation triangle is the sequential telescope map. -/
@[simp]
theorem Presentation.triangle.mor₁ {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.triangle.mor₁ = CoproductCocone.telescopeMap K P.coproduct := sorry

/-- The second morphism of a presentation triangle is induced by its structure maps. -/
@[simp]
theorem Presentation.triangle.mor₂ {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.triangle.mor₂ = P.toCocone := sorry

/-- The third morphism of a presentation triangle is its stored connecting morphism. -/
@[simp]
theorem Presentation.triangle.mor₃ {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.triangle.mor₃ = P.connecting := sorry

/-- The telescope triangle encoded by a presentation is distinguished. -/
@[stacks 090Z]
theorem Presentation.triangle.distinguished {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.triangle ∈ distTriang D := sorry

/-- The structure maps in a telescope presentation are natural along every morphism of the
sequential indexing category. -/
@[reassoc]
theorem Presentation.ι_naturality {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) {m n : ℕ} (h : m ≤ n) :
    K.map (homOfLE h) ≫ P.ι n = P.ι m := sorry

/-- The successor specialization of naturality for the structure maps in a telescope
presentation. -/
@[reassoc]
theorem Presentation.ι_naturality_succ {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    K.map (homOfLE (Nat.le_succ n)) ≫ P.ι (n + 1) = P.ι n := sorry

/-- The presentation legs satisfy the naturality equation for the associated cocone. -/
theorem Presentation.cocone.naturality {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    K.map (homOfLE (Nat.le_succ n)) ≫ P.ι (n + 1) =
      P.ι n ≫ ((Functor.const ℕ).obj X).map (homOfLE (Nat.le_succ n)) := sorry

/-- The cocone over the sequential diagram determined by a telescope presentation. -/
def Presentation.cocone {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) : Cocone K :=
  Cocone.mk X <| NatTrans.ofSequence P.ι (Presentation.cocone.naturality P)

/-- The point of the cocone associated to a telescope presentation is its cone object. -/
@[simp]
theorem Presentation.cocone.pt {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.cocone.pt = X := sorry

/-- The legs of the cocone associated to a telescope presentation are its stored structure maps. -/
@[simp, reassoc]
theorem Presentation.cocone.ι_app {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.cocone.ι.app n = P.ι n := sorry

/-- A telescope presentation determines the intrinsic homotopy-colimit predicate. -/
theorem Presentation.isOf {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    HomotopyColimit.IsOf K X := sorry

namespace IsOf

/-- The intrinsic homotopy-colimit predicate is equivalent to nonempty explicit presentation
data. -/
@[stacks 090Z]
theorem nonemptyPresentation_iff {K : ℕ ⥤ D} {X : D} :
    HomotopyColimit.IsOf K X ↔ Nonempty (Presentation K X) := sorry

/-- An intrinsic homotopy-colimit witness supplies a presentation nonemptily, without making a
public choice. -/
theorem nonemptyPresentation {K : ℕ ⥤ D} {X : D}
    (h : HomotopyColimit.IsOf K X) : Nonempty (Presentation K X) := sorry

/-- Nonempty explicit presentation data implies the intrinsic homotopy-colimit predicate. -/
theorem ofNonemptyPresentation {K : ℕ ⥤ D} {X : D}
    (h : Nonempty (Presentation K X)) : HomotopyColimit.IsOf K X := sorry

end IsOf

end CategoryTheory.HomotopyColimit
