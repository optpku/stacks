module

public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.CompactOpen.Intersection
public import ReasLib.Topology.Sheaves.InverseLimit.PullbackSections

/-!
# Sections over directed intersections of compact opens

This module constructs the canonical comparison from the filtered colimit of sections on a
downward-directed family of compact opens to sections on its intersection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe w

namespace TopCat.Sheaf.CompactOpen.Intersection

variable {C : Type (w + 1)} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X : TopCat.{w}}

/-- The diagram `U ↦ F(U)` on the opposite of a family of compact opens. -/
abbrev diagram (S : Set (CompactOpens X)) (F : X.Sheaf C) : Sᵒᵖ ⥤ C :=
  (compactOpenFamilyToOpens S).toFunctor.op ⋙ F.presheaf

/-- Sections over the top open after restricting `F` to the subspace carried by `W`. -/
abbrev target (W : Set X) (F : X.Sheaf C) : C :=
  ((TopCat.Sheaf.pullback C (TopCat.subsetInclusion W)).obj F).presheaf.obj
    (op (⊤ : Opens (TopCat.subsetSpace W)))

/-- The inverse image in the intersection subspace of every displayed compact open is the top
open. -/
theorem preimage_eq_top {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (U : S) :
    (Opens.map (TopCat.subsetInclusion W)).obj U.1.toOpens =
      (⊤ : Opens (TopCat.subsetSpace W)) :=
  Opens.ext (Set.eq_univ_of_forall fun x ↦
    Set.mem_iInter.mp
      (Set.mem_iInter.mp
        (Eq.mp (congrArg (fun T : Set X ↦ x.1 ∈ T) h.eq_iInter) x.property) U.1)
      U.property)

/-- Transport sections over the inverse image of a displayed compact open to sections over the
top open of the intersection subspace. -/
noncomputable def preimageTopIso {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C) (U : S) :
    ((TopCat.Sheaf.pullback C (TopCat.subsetInclusion W)).obj F).presheaf.obj
        (op ((Opens.map (TopCat.subsetInclusion W)).obj U.1.toOpens)) ≅
      target W F :=
  eqToIso (congrArg
    (fun V ↦ ((TopCat.Sheaf.pullback C
      (TopCat.subsetInclusion W)).obj F).presheaf.obj (op V))
    (preimage_eq_top h U))

/-- The canonical restriction map from sections on a displayed compact open to sections on the
intersection subspace. -/
noncomputable def stageMap {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C) (U : S) :
    (diagram S F).obj (op U) ⟶ target W F :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction C
      (TopCat.subsetInclusion W)).unit.app F).1.app (op U.1.toOpens)) ≫
    (preimageTopIso h F U).hom

/-- Restriction maps between displayed compact opens commute with their canonical maps to
sections on the intersection subspace. -/
theorem stageMap_naturality {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C)
    {U V : Sᵒᵖ} (f : U ⟶ V) :
    (diagram S F).map f ≫ stageMap h F V.unop =
      stageMap h F U.unop ≫ ((Functor.const Sᵒᵖ).obj (target W F)).map f := sorry

/-- The canonical cocone from compact-open stage sections to sections on the intersection
subspace. -/
noncomputable def cocone {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C) :
    Cocone (diagram S F) where
  pt := target W F
  ι :=
    { app U := stageMap h F U.unop
      naturality _ _ f := stageMap_naturality h F f }

/-- The canonical map from the colimit of compact-open stage sections to sections on the
intersection subspace. -/
noncomputable def comparison {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C) :
    colimit (diagram S F) ⟶ target W F :=
  colimit.desc (diagram S F) (cocone h F)

/-- The compact-open intersection comparison restricts at every stage to the canonical
restriction map. -/
@[reassoc]
theorem ι_comp_comparison {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C) (U : Sᵒᵖ) :
    colimit.ι (diagram S F) U ≫ comparison h F = stageMap h F U.unop := sorry

/-- For a quasi-separated prespectral, quasi-sober `T₀` space, the canonical comparison from
the colimit of sections over a compact-open directed-intersection presentation to sections on
the intersection is an isomorphism. -/
theorem comparison_isIso [T0Space X] [QuasiSober X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C) :
    IsIso (comparison h F) := sorry

end TopCat.Sheaf.CompactOpen.Intersection
