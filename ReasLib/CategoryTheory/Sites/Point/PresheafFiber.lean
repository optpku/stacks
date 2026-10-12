/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.Cofiltered
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.PresheafFiber

/-!
# Stagewise cocones for inverse-system presheaf fibers

This module exposes the colimit presentation of the presheaf fiber of an
essentially-small cofiltered inverse system. The directed-preorder case is a
thin specialization. The construction is independent of a Grothendieck
topology and can be used by any construction based on
`ofIsCofiltered.fiber`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w q w₀ w₁ v₀ v₁

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace Directed

-- This bridge is implementation-local: the fiber universe is chosen to contain the index type.
attribute [local instance] initiallySmall_of_essentiallySmall

/-- The stagewise section diagram of an inverse system is naturally isomorphic to the element
diagram restricted along its canonical initial functor. -/
noncomputable def stageDiagramIso
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    S.op ⋙ F ≅
      (functor.{max u v w} S).op ⋙
        (CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- The raw presheaf fiber of a directed inverse system as a cocone over its original stagewise
section diagram. -/
noncomputable def stageCocone
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    Cocone (S.op ⋙ F) :=
  (Cocone.precompose (stageDiagramIso S F).hom).obj
    ((colimit.cocone ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F)).whisker
      (functor.{max u v w} S).op)

/-- The canonical stagewise cocone computes the raw presheaf fiber of a directed inverse system. -/
noncomputable def stageIsColimit
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    IsColimit (stageCocone S F) :=
  (IsColimit.precomposeHomEquiv (stageDiagramIso S F)
    ((colimit.cocone ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F)).whisker
      (functor.{max u v w} S).op)).symm
    ((Functor.Final.isColimitWhiskerEquiv (functor.{max u v w} S).op
      (colimit.cocone ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F))).2
      (colimit.isColimit ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F)))

/-- The colimit of stagewise sections of a directed inverse system is its canonical-universe
presheaf fiber.  This is the downstream-facing form of `stageIsColimit`; it avoids
exposing the implementation-level `fiber` universe. -/
noncomputable def stageColimitIso
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    colimit (S.op ⋙ F) ≅ (EssentiallySmallFiber.presheafFiberMax S).obj F :=
  (colimit.isColimit (S.op ⋙ F)).coconePointUniqueUpToIso
    (stageIsColimit S F)

/-- Two elements of the presheaf fiber of a nonempty directed inverse system admit a common
presentation at one object and one fiber element. -/
theorem jointlySurjective₂
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type (max u v w)}
    (x y : (fiber.{max u v w} S).presheafFiber.obj F) :
    ∃ (X : C) (u : (fiber.{max u v w} S).obj X) (z z' : F.obj (op X)),
      (fiber.{max u v w} S).toPresheafFiber X u F z = x ∧
      (fiber.{max u v w} S).toPresheafFiber X u F z' = y := sorry

/-- Equality of two stage generators in a raw presheaf fiber is witnessed
after restricting both sections to one common object of the inverse-system
fiber. -/
theorem generatorEq_iff
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [InitiallySmall ιᵒᵖ] (S : ιᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type (max u v w)}
    (X : C) (x : (fiber.{max u v w} S).obj X) (z₁ z₂ : F.obj (op X)) :
    (fiber.{max u v w} S).toPresheafFiber X x F z₁ =
        (fiber.{max u v w} S).toPresheafFiber X x F z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : (fiber.{max u v w} S).obj Y),
        (fiber.{max u v w} S).map f y = x ∧ F.map f.op z₁ = F.map f.op z₂ := sorry

end Directed

namespace EssentiallySmallFiber

variable {I : Type w₀} [Category.{v₀} I]
variable [LocallySmall.{q} C] [EssentiallySmall.{q} Iᵒᵖ]

section CanonicalUniverse

variable {I : Type w₀} [Category.{v₀} I]
variable [LocallySmall.{max u v w₀ v₀} C]
variable [EssentiallySmall.{max u v w₀ v₀} Iᵒᵖ]

/-- The canonical generator in the universe selected by `fiberMax`.  This is the ergonomic
specialization of `mk`; downstream statements should use it instead of exposing the fiber
universe parameters of the underlying `fiber` construction. -/
noncomputable abbrev mkMax {S : Iᵒᵖ ⥤ C} {U : Iᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (EssentiallySmallFiber.fiberMax S).obj W :=
  mk.{u, v, max u v w₀ v₀, w₀, v₀} f

/-- The canonical map from a stage section into the `presheafFiberMax` of an essentially-small
inverse system. -/
noncomputable abbrev toPresheafFiberMax
    (S : Iᵒᵖ ⥤ C) (X : C) (x : (EssentiallySmallFiber.fiberMax S).obj X)
    (F : Cᵒᵖ ⥤ Type (max u v w₀ v₀)) :
    F.obj (op X) ⟶ (EssentiallySmallFiber.presheafFiberMax S).obj F :=
  toPresheafFiber.{u, v, max u v w₀ v₀, w₀, v₀} S X x F

end CanonicalUniverse

/-- Two elements of a presheaf fiber whose category of elements is cofiltered
admit a common fiber-generator presentation. -/
theorem jointlySurjective₂
    (S : Iᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type q}
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
    [IsCofiltered (EssentiallySmallFiber.fiber S).Elements]
    (x y : (EssentiallySmallFiber.presheafFiber S).obj F) :
    ∃ (X : C) (u : (EssentiallySmallFiber.fiber S).obj X) (z z' : F.obj (op X)),
      toPresheafFiber S X u F z = x ∧ toPresheafFiber S X u F z' = y := sorry

/-- Equality of two generators in a presheaf fiber whose category of elements
is cofiltered is witnessed after restricting both to one common fiber object. -/
theorem toPresheafFiber_eq_iff
    (S : Iᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type q}
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
    [IsCofiltered (EssentiallySmallFiber.fiber S).Elements]
    (X : C) (x : (EssentiallySmallFiber.fiber S).obj X) (z₁ z₂ : F.obj (op X)) :
    toPresheafFiber S X x F z₁ = toPresheafFiber S X x F z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : (EssentiallySmallFiber.fiber S).obj Y),
        (EssentiallySmallFiber.fiber S).map f y = x ∧ F.map f.op z₁ = F.map f.op z₂ := sorry

section OfIsCofiltered

variable [IsCofiltered Iᵒᵖ]

/-- The source-cofiltered specialization of `jointlySurjective₂`. -/
theorem Cofiltered.jointlySurjective₂
    (S : Iᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type q}
    (x y : (EssentiallySmallFiber.Cofiltered.presheafFiber S).obj F) :
    ∃ (X : C) (u : (EssentiallySmallFiber.fiber S).obj X) (z z' : F.obj (op X)),
      Cofiltered.toPresheafFiber S X u F z = x ∧
        Cofiltered.toPresheafFiber S X u F z' = y := sorry

/-- The source-cofiltered specialization of `toPresheafFiber_eq_iff`. -/
theorem Cofiltered.toPresheafFiber_eq_iff
    (S : Iᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type q}
    (X : C) (x : (EssentiallySmallFiber.fiber S).obj X) (z₁ z₂ : F.obj (op X)) :
    Cofiltered.toPresheafFiber S X x F z₁ =
        Cofiltered.toPresheafFiber S X x F z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : (EssentiallySmallFiber.fiber S).obj Y),
        (EssentiallySmallFiber.fiber S).map f y = x ∧ F.map f.op z₁ = F.map f.op z₂ := sorry

end OfIsCofiltered

end EssentiallySmallFiber

namespace EssentiallySmallFiber

section CanonicalDirectedPresentation

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable [LocallySmall.{max u v w} C]

/-- The stage injection followed by `Directed.stageColimitIso` is the canonical germ attached
to the identity map at that stage. -/
@[simp]
theorem stageColimitIso_ι_hom
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) (i : ι)
    (t : F.obj (op (S.obj (op i)))) :
    (Directed.stageColimitIso S F).hom
        (colimit.ι (S.op ⋙ F) (op (op i)) t) =
      toPresheafFiberMax S (S.obj (op i))
        (mkMax (S := S) (𝟙 (S.obj (op i)))) F t := sorry

end CanonicalDirectedPresentation

end EssentiallySmallFiber

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
