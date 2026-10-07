module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Predecessor
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.RestrictionFunctor

/-!
# Top-stage diagrams from compatible prefix sections

A section of the inverse system of open prefixes below a cut determines a
coherent based diagram: at each predecessor, take the greatest stage of that
prefix.  This leaf owns that construction and its computation and realization
API.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z} [Preorder M]

/-- The inverse system of open prefixes at all strict predecessors of a fixed
cut. -/
noncomputable def belowFunctor
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) (cut : WithTop (WithBot M)) :
    (Set.Iio cut)ᵒᵖ ⥤ Type _ :=
  (OrderHom.Subtype.val (· ∈ Set.Iio cut)).monotone.functor.op ⋙
    restrictionFunctor (J := J) A request

variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}
variable {cut : WithTop (WithBot M)}

namespace belowFunctor

/-- The predecessor-prefix functor acts on an index morphism by restricting
the later prefix to the earlier cut. -/
@[simp]
theorem map_apply {c d : (Set.Iio cut)ᵒᵖ} (f : c ⟶ d)
    (D : Stage.Scheduled.OpenPrefix (J := J) A request c.unop.1) :
    (belowFunctor (J := J) A request cut).map f D =
      D.restrict (leOfHom f.unop) := sorry

end belowFunctor

namespace Section

variable (s : (belowFunctor (J := J) A request cut).sections)

/-- Section compatibility says that the prefix at an earlier predecessor is
the restriction of the prefix at a later predecessor. -/
theorem restrict {c d : Set.Iio cut} (hcd : c ≤ d) :
    (s.val (op d)).restrict hcd = s.val (op c) := sorry

/-- The greatest stage of the prefix selected by a section at a strict
predecessor of the cut. -/
abbrev topStage (c : Set.Iio cut) :
    Stage.{u, v, q, r, r'} (J := J) S P x y :=
  (s.val (op c)).toDiagram.stage ⟨c.1, le_rfl⟩

namespace topStage

/-- The stage at an earlier predecessor, viewed inside a later section value,
is the top stage of the earlier section value. -/
theorem eqOfLE {c d : Set.Iio cut} (hcd : c ≤ d) :
    (s.val (op d)).toDiagram.stage ⟨c.1, hcd⟩ =
      topStage s c := sorry

end topStage

/-- The canonical transition between the top stages of two comparable section
values. -/
noncomputable def topHom {c d : Set.Iio cut} (hcd : c ≤ d) :
    topStage s c ⟶ topStage s d :=
  eqToHom (congrArg
    (fun E : OpenPrefix (J := J) A request c.1 =>
      E.toDiagram.stage ⟨c.1, le_rfl⟩)
    (s.property ((homOfLE hcd).op))).symm ≫
    (s.val (op d)).toDiagram.hom
      (show (⟨c.1, hcd⟩ : {i : WithTop (WithBot M) // i ≤ d.1}) ≤
        ⟨d.1, le_rfl⟩ from hcd)

namespace topHom

/-- The top-stage transition at a reflexive comparison is the identity. -/
theorem refl (c : Set.Iio cut) :
    topHom s (le_rfl : c ≤ c) =
      𝟙 (topStage s c) := sorry

/-- Top-stage transitions compose along chains of predecessors. -/
theorem comp {c d e : Set.Iio cut} (hcd : c ≤ d) (hde : d ≤ e) :
    topHom s (le_trans hcd hde) = topHom s hcd ≫ topHom s hde := sorry

end topHom

/-- The top stages of a compatible prefix section form a functor on the strict
predecessors of the cut. -/
noncomputable def topFunctor : Set.Iio cut ⥤
    Stage.{u, v, q, r, r'} (J := J) S P x y where
  obj c := topStage s c
  map f := topHom s (leOfHom f)
  map_id c := topHom.refl s c
  map_comp f g := topHom.comp s (leOfHom f) (leOfHom g)

/-- The base leg from the initial stage to the section's greatest stage at a
strict predecessor. -/
abbrev topBase (c : Set.Iio cut) : A ⟶ topStage s c :=
  (s.val (op c)).toDiagram.fromBase ⟨c.1, le_rfl⟩

namespace topBase

/-- The base legs to section top stages are natural with respect to the
canonical top-stage transitions. -/
theorem naturality {c d : Set.Iio cut} (f : c ⟶ d) :
    ((Functor.const (Set.Iio cut)).obj A).map f ≫
        topBase s d = topBase s c ≫ topHom s (leOfHom f) := sorry

end topBase

/-- The coherent based diagram of top stages extracted from a compatible
section of predecessor prefixes. -/
noncomputable def topDiagram :
    Stage.Diagram (J := J) A (Set.Iio cut) where
  functor := topFunctor s
  base := {
    app := topBase s
    naturality := fun _ _ f => topBase.naturality s f
  }

namespace topDiagram

/-- The stage of the extracted top diagram is the top stage of the
corresponding section prefix. -/
@[simp]
theorem stage (c : Set.Iio cut) :
    (topDiagram s).stage c = topStage s c := sorry

/-- A transition of the extracted top diagram is the canonical top-stage
transition. -/
@[simp]
theorem hom {c d : Set.Iio cut} (hcd : c ≤ d) :
    (topDiagram s).hom hcd = topHom s hcd := sorry

/-- A base leg of the extracted top diagram is the top base leg of the
corresponding section prefix. -/
@[simp]
theorem fromBase (c : Set.Iio cut) :
    (topDiagram s).fromBase c = topBase s c := sorry

/-- The top-stage diagram extracted from a prefix section realizes every
request required before each predecessor. -/
theorem realizes :
    PredecessorRealizes (request := request) (topDiagram s) := sorry

end topDiagram

/- The top transition consumes the compatibility proof already stored by the
section. The remaining `sorryAx` is confined to equality and functor/naturality
law fields. -/

end Section
end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
