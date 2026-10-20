module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import ReasLib.Topology.Sheaves.Basis.Neighborhoods
public import ReasLib.Topology.Sheaves.Basis.Cover

/-!
# Stalks of sheaves on a topological basis

This file constructs stalks directly as colimits over basis neighborhoods and describes
sections by their locally representable families of germs.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u v

namespace BasisSheaf

variable {X : Type u} [TopologicalSpace X] {B : Set (Opens X)}

/-
Stalks of a sheaf defined only on a basis need a direct construction: mathlib's
`TopCat.Presheaf.stalk` is indexed by all open neighborhoods, while the project basis-extension
API uses a different `TopCat`-bundled sheaf owner. We therefore retain the direct colimit over basis neighborhoods,
generalized by allowing arbitrary collections `B`. This keeps the germ map explicit for later
basis-sheaf arguments.
-/
/-- The diagram of sections over basis neighborhoods of `x`. -/
abbrev stalkDiagram (F : BasisSheaf.{u, max u v} B) (x : X) :
    (BasisOpenNhds (X := TopCat.of X) B x)ᵒᵖ ⥤ Type (max u v) :=
  (basisOpenNhdsInclusion (X := TopCat.of X) B x).op ⋙ F.obj

/-- The stalk of a basis sheaf at `x`, as the colimit over basis neighborhoods. -/
abbrev stalk (F : BasisSheaf.{u, max u v} B) (x : X) : Type (max u v) :=
  colimit (stalkDiagram F x)

/-- The germ in the basis stalk at `x` of a section over a basis open `U` containing `x`. -/
abbrev germ (F : BasisSheaf.{u, max u v} B) (U : BasisOpen B) (x : U.1) :
    F.obj.obj (op U) → F.stalk x.1 :=
  colimit.ι (stalkDiagram F x.1) (op ⟨U, x.2⟩)

/-- A family of basis-stalk elements on `U` is locally represented by sections on basis opens
contained in `U`. -/
def IsLocallyRepresentable (F : BasisSheaf.{u, max u v} B) (U : BasisOpen B)
    (t : ∀ x : U.1, F.stalk x.1) : Prop :=
  ∀ x : U.1,
    ∃ (V : BasisOpen B) (i : V ⟶ U) (_ : x.1 ∈ V.1) (s : F.obj.obj (op V)),
      ∀ y : V.1, t ⟨y.1, i.hom.le y.2⟩ = F.germ V y s

/-- The family of basis-stalk germs associated to a section over `U`. -/
abbrev sectionToStalkFamily (F : BasisSheaf.{u, max u v} B) (U : BasisOpen B) :
    F.obj.obj (op U) → ∀ x : U.1, F.stalk x.1 :=
  fun s x ↦ F.germ U x s

/-
The source says that taking germs identifies sections with exactly the locally represented
families. `Set.BijOn` expresses that identification directly, without introducing a subtype-valued
wrapper or a duplicate `Function.Bijective` theorem. The topological-basis hypothesis is retained
precisely at this theorem, where it supplies common refinements and basis covers for gluing.
-/
/-- For a sheaf of sets `F` on a topological basis `B` and `U ∈ B`, taking germs
identifies sections on `U` with the families of stalk elements that are locally represented by a
section on some basis neighborhood inside `U` at every point. -/
theorem sections_bijOn_locallyRepresentableFamilies
    (F : BasisSheaf.{u, max u v} B) (hB : Opens.IsBasis B) (U : BasisOpen B) :
    Set.BijOn (F.sectionToStalkFamily U) Set.univ
      { t : ∀ x : U.1, F.stalk x.1 | F.IsLocallyRepresentable U t } := sorry
/- Proof strategy: prove injectivity by representing equality of two colimit germs on a common
basis neighborhood, using `Types.FilteredColimit.colimit_eq_iff` after showing the opposite basis-
neighborhood category is filtered from `hB`; the basis-sheaf uniqueness axiom then identifies the
sections. For surjectivity, choose the local representatives from `IsLocallyRepresentable`, form a
`BasisCover`, use the same filtered-colimit equality criterion to prove compatibility on the
`intersectionBasisCover` refinements, and apply `F.property` to glue. -/

end BasisSheaf
