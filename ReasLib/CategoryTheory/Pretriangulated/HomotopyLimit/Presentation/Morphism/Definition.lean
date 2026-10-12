/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Definition of Morphisms of Homotopy-Limit Presentations

The data owner for a compatible map of explicit Milnor presentations over a morphism of
sequential inverse systems, together with equality and reindexing along equality of tower maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A morphism between homotopy-limit presentations over a morphism of sequential inverse
systems. It records the map of presented objects and the two squares needed for the associated
morphism of Milnor triangles. -/
@[stacks 08TC "morphism of homotopy-limit presentations"]
structure Presentation.Hom {K L : SequentialInverseSystem D} (α : K ⟶ L)
    {X Y : D} (P : Presentation K X) (Q : Presentation L Y) where
  /-- The map between the presented homotopy-limit objects. -/
  hom : X ⟶ Y
  /-- Compatibility with the inclusions into the explicitly retained product cones. -/
  ιComm : CommSq P.ι hom (ProductCone.map P.product Q.product α) Q.ι
  /-- Compatibility with the connecting maps and the shifted map of presented objects. -/
  connectingComm :
    CommSq P.connecting (ProductCone.map P.product Q.product α)
      (hom⟦(1 : ℤ)⟧') Q.connecting

namespace Presentation.Hom

/-- Two morphisms of homotopy-limit presentations are equal when their maps between the
presented objects are equal. -/
@[ext]
theorem ext {K L : SequentialInverseSystem D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y} {φ ψ : Hom α P Q}
    (h : φ.hom = ψ.hom) : φ = ψ := sorry

/-- Reindex a morphism of homotopy-limit presentations along an equality of the underlying
tower morphisms. -/
def rebase {K L : SequentialInverseSystem D} {α β : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (h : α = β) (φ : Hom α P Q) : Hom β P Q :=
  h ▸ φ

/-- Rebasing does not change the map between the presented objects. -/
@[simp]
theorem rebase_hom {K L : SequentialInverseSystem D} {α β : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (h : α = β) (φ : Hom α P Q) :
    (rebase h φ).hom = φ.hom := sorry

/-- Rebasing along reflexivity is the identity operation. -/
@[simp]
theorem rebase_rfl {K L : SequentialInverseSystem D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y} (φ : Hom α P Q) :
    rebase rfl φ = φ := sorry

end Presentation.Hom

end CategoryTheory.HomotopyLimit
