module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage.Category

/-!
# Basic based diagrams of saturation stages

This leaf gives the categorical owner for a coherent family of scheduled
separating refinements.  A diagram is a functor from a preorder together with
a natural transformation from a fixed base stage; it is independent of any
particular recursion, request enumeration, or Chapter 7 presentation.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace Stage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

/-- A coherent diagram of scheduled saturation stages based at `A`.

The functor owns the stage values and transition refinements.  `fromBase` is
the canonical compatible refinement from `A` to every diagram stage. -/
structure Diagram
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (κ : Type z) [Preorder κ] where
  /-- The scheduled saturation stage at each diagram index. -/
  functor : κ ⥤ Stage.{u, v, q, r, r'} (J := J) S P x y
  /-- The natural transformation of compatible maps from the fixed base stage. -/
  base : (Functor.const κ).obj A ⟶ functor

namespace Diagram

variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {κ : Type z} [Preorder κ]

/-- Based stage diagrams are determined by their functor and compatible base map. -/
@[ext]
theorem ext {D E : Diagram (J := J) A κ}
    (hfunctor : D.functor = E.functor) (hbase : HEq D.base E.base) :
    D = E := sorry

/-- The stage at one index of a based saturation-stage diagram. -/
abbrev stage (D : Diagram (J := J) A κ) (i : κ) :=
  D.functor.obj i

/-- The transition refinement attached to an order comparison of diagram indices. -/
abbrev hom (D : Diagram (J := J) A κ) {i j : κ} (hij : i ≤ j) :
    D.stage i ⟶ D.stage j :=
  D.functor.map (homOfLE hij)

/-- The compatible refinement from the base stage to one diagram stage. -/
abbrev fromBase (D : Diagram (J := J) A κ) (i : κ) : A ⟶ D.stage i :=
  D.base.app i

namespace hom

/-- A reflexive diagram transition is the identity stage morphism. -/
@[simp]
theorem refl (D : Diagram (J := J) A κ) (i : κ) :
    D.hom (le_rfl : i ≤ i) = 𝟙 (D.stage i) := sorry

/-- Diagram transitions compose along chains of indices. -/
@[simp]
theorem comp (D : Diagram (J := J) A κ)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    D.hom (le_trans hij hjk) = D.hom hij ≫ D.hom hjk := sorry

end hom

namespace fromBase

/-- Base refinements commute with every diagram transition. -/
theorem comp (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) :
    D.fromBase j = D.fromBase i ≫ D.hom hij := sorry

/-- Transporting a source request along a later base leg agrees with transport through an
earlier base leg followed by the intervening diagram transition. -/
theorem mapRequest (D : Diagram (J := J) A κ)
    {i j : κ} (hij : i ≤ j) (request : A.target.Request J) :
    (D.fromBase j).mapRequest request =
      (D.hom hij).mapRequest ((D.fromBase i).mapRequest request) := sorry

end fromBase

end Diagram

end Stage
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
