/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.CompactOpen.Intersection

/-!
# Differences of directed compact-open intersections

This module is the topology- and category-theory-only difference layer for a compact-open
directed-intersection presentation. It works for an arbitrary displayed intersection `W`; the
specialization `W = nhdsKer E` is intentionally deferred to
`ReasLib.Topology.Spectral.SpecializingPoints`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

namespace TopCat

variable {Y : TopCat.{u}}

/-- The map `W \ E ⟶ Eᶜ` induced by the inclusions of subsets is continuous. -/
theorem continuous_sdiffInclusion (W E : Set Y) :
    Continuous (fun x : (W \ E : Set Y) ↦ (⟨x.1, x.2.2⟩ : (Eᶜ : Set Y))) := sorry

/-- The canonical inclusion of `W \ E` into the fixed complement subspace `Eᶜ`. -/
@[stacks 0A3D "difference inclusion into the fixed complement"]
def sdiffInclusion (W E : Set Y) : subsetSpace (W \ E) ⟶ subsetSpace Eᶜ :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_sdiffInclusion W E⟩

/-- The inclusion `W \ E ⟶ Eᶜ` preserves the ambient point. -/
@[simp]
theorem sdiffInclusion_apply (W E : Set Y) (x : subsetSpace (W \ E)) :
    (sdiffInclusion W E x).1 = x.1 := sorry

/-- Inclusion into `Eᶜ` followed by inclusion into the ambient space is the direct subset
inclusion of `W \ E`. -/
@[simp]
theorem sdiffInclusion_comp_subsetInclusion (W E : Set Y) :
    sdiffInclusion W E ≫ subsetInclusion Eᶜ = subsetInclusion (W \ E) := sorry

end TopCat

namespace TopologicalSpace.CompactOpens

/-- A compact open `U` determines the open subset `U \ E` of the fixed complement subspace
`Eᶜ`. -/
@[stacks 0A3D "compact-open difference in the fixed complement"]
def sdiffOpen (U : CompactOpens X) (E : Set X) :
    Opens (TopCat.subsetSpace (X := TopCat.of X) Eᶜ) :=
  ⟨(fun x : (Eᶜ : Set X) ↦ x.1) ⁻¹' (U : Set X),
    U.isOpen.preimage continuous_subtype_val⟩

/-- Membership in `U.sdiffOpen E` means that the ambient point belongs to `U`. -/
@[simp]
theorem mem_sdiffOpen (U : CompactOpens X) (E : Set X)
    (x : TopCat.subsetSpace (X := TopCat.of X) Eᶜ) :
    x ∈ U.sdiffOpen E ↔ x.1 ∈ (U : Set X) := sorry

end TopologicalSpace.CompactOpens

namespace TopologicalSpace.CompactOpenFamily

/-- Taking `U \ E` inside the fixed complement subspace is monotone in a compact-open family. -/
theorem sdiffToOpens_monotone (S : Set (CompactOpens X)) (E : Set X) :
    Monotone (fun U : S ↦ U.1.sdiffOpen E) := sorry

/-- A family of compact opens, viewed as the corresponding monotone family of opens `U \ E`
inside the single ambient space `Eᶜ`. -/
@[stacks 0A3D "compact-open difference family in the fixed complement"]
def sdiffToOpens (S : Set (CompactOpens X)) (E : Set X) :
    S →o Opens (TopCat.subsetSpace (X := TopCat.of X) Eᶜ) :=
  ⟨fun U ↦ U.1.sdiffOpen E, sdiffToOpens_monotone S E⟩

/-- Evaluating the fixed-complement family returns the open `U \ E`. -/
@[simp]
theorem sdiffToOpens_apply (S : Set (CompactOpens X)) (E : Set X) (U : S) :
    sdiffToOpens S E U = U.1.sdiffOpen E := sorry

end TopologicalSpace.CompactOpenFamily

namespace IsCompactOpenDirectedIntersection

/-- If `W` is the displayed intersection, the inverse image of every stage open `U \ E` under
`W \ E ⟶ Eᶜ` is the top open. -/
@[stacks 0A3D "difference-stage inverse image is top"]
theorem map_sdiffOpen_eq_top
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) (U : S) :
    (Opens.map (TopCat.sdiffInclusion (Y := TopCat.of X) W E)).obj (U.1.sdiffOpen E) =
      (⊤ : Opens (TopCat.subsetSpace (X := TopCat.of X) (W \ E))) := sorry

end IsCompactOpenDirectedIntersection

/-- The inclusion `U \ E ⟶ V \ E` induced by an inclusion of compact opens is continuous. -/
theorem continuous_compactOpenSdiffInclusion
    (E : Set X) {U V : CompactOpens X} (hUV : U ≤ V) :
    Continuous (fun x : ((U : Set X) \ E : Set X) ↦
      (⟨x.1, ⟨hUV x.2.1, x.2.2⟩⟩ : ((V : Set X) \ E : Set X))) := sorry

/-- The inclusion morphism `U \ E ⟶ V \ E` induced by an inclusion of compact opens. -/
def compactOpenSdiffInclusion
    (E : Set X) {U V : CompactOpens X} (hUV : U ≤ V) :
    TopCat.of ((U : Set X) \ E : Set X) ⟶ TopCat.of ((V : Set X) \ E : Set X) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, ⟨hUV x.2.1, x.2.2⟩⟩,
      continuous_compactOpenSdiffInclusion E hUV⟩

/-- A difference-stage inclusion preserves the ambient point. -/
theorem compactOpenSdiffInclusion_apply
    (E : Set X) {U V : CompactOpens X} (hUV : U ≤ V)
    (x : ((U : Set X) \ E : Set X)) :
    (compactOpenSdiffInclusion E hUV x).1 = x.1 := sorry

/-- The difference inclusion associated to an identity stage morphism is the identity. -/
theorem compactOpenSdiffInclusion_id
    (E : Set X) {S : Set (CompactOpens X)} (U : S) :
    compactOpenSdiffInclusion E (leOfHom (𝟙 U)) =
      𝟙 (TopCat.of ((U.1 : Set X) \ E : Set X)) := sorry

/-- Difference inclusions respect composition of stage morphisms. -/
theorem compactOpenSdiffInclusion_comp
    (E : Set X) {S : Set (CompactOpens X)}
    {U V T : S} (f : U ⟶ V) (g : V ⟶ T) :
    compactOpenSdiffInclusion E (leOfHom (f ≫ g)) =
      compactOpenSdiffInclusion E (leOfHom f) ≫
        compactOpenSdiffInclusion E (leOfHom g) := sorry

/-- The diagram of stage differences `U \ E` and their inclusion maps. -/
@[stacks 0AP0 "compact-open difference diagram"]
def compactOpenSdiffDiagram
    (E : Set X) (S : Set (CompactOpens X)) : S ⥤ TopCat where
  obj U := TopCat.of ((U.1 : Set X) \ E : Set X)
  map f := compactOpenSdiffInclusion E (leOfHom f)
  map_id U := compactOpenSdiffInclusion_id E U
  map_comp f g := compactOpenSdiffInclusion_comp E f g

namespace IsCompactOpenDirectedIntersection

/-- The canonical map `W \ E ⟶ U \ E` to a stage in a compact-open directed-intersection
presentation is continuous. -/
theorem continuous_sdiffConeApp
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) (U : S) :
    Continuous (fun x : (W \ E : Set X) ↦
      (⟨x.1, ⟨h.mem x.2.1 U.2, x.2.2⟩⟩ : ((U.1 : Set X) \ E : Set X))) := sorry

/-- The canonical projection `W \ E ⟶ U \ E` to one compact-open difference stage. -/
def sdiffConeApp
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) (U : S) :
    TopCat.of (W \ E : Set X) ⟶ TopCat.of ((U.1 : Set X) \ E : Set X) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, ⟨h.mem x.2.1 U.2, x.2.2⟩⟩,
      continuous_sdiffConeApp h E U⟩

/-- A difference-stage projection preserves the ambient point. -/
theorem sdiffConeApp_apply
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) (U : S)
    (x : (W \ E : Set X)) :
    (sdiffConeApp h E U x).1 = x.1 := sorry

/-- The projections from `W \ E` are natural in the compact-open stage. -/
theorem sdiffCone_naturality
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    {U V : S} (f : U ⟶ V) :
    ((Functor.const S).obj (TopCat.of (W \ E : Set X))).map f ≫
        sdiffConeApp h E V =
      sdiffConeApp h E U ≫
        (compactOpenSdiffDiagram E S).map f := sorry

/-- The canonical cone from `W \ E` to the diagram of compact-open stage differences. -/
@[stacks 0AP0 "directed compact-open difference cone"]
def sdiffCone
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) :
    Cone (compactOpenSdiffDiagram E S) where
  pt := TopCat.of (W \ E : Set X)
  π :=
    { app := sdiffConeApp h E
      naturality := fun _ _ f ↦ sdiffCone_naturality h E f }

/-- The ambient value of the canonical lift to `W \ E`, computed at one chosen stage. -/
noncomputable def sdiffLiftValue
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) (x : c.pt) : X :=
  (c.π.app (⟨h.nonempty.choose, h.nonempty.choose_spec⟩ : S) x).1

/-- The ambient lift value agrees with evaluation at every stage difference. -/
theorem sdiffLiftValue_eq
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) (U : S) (x : c.pt) :
    sdiffLiftValue h E c x = (c.π.app U x).1 := sorry

/-- The ambient value of a compatible cone belongs to `W \ E`. -/
theorem sdiffLiftValue_mem
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) (x : c.pt) :
    sdiffLiftValue h E c x ∈ W \ E := sorry

/-- The underlying function of the canonical lift to `W \ E`. -/
noncomputable def sdiffLiftFun
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) :
    c.pt → (W \ E : Set X) :=
  fun x ↦ ⟨sdiffLiftValue h E c x, sdiffLiftValue_mem h E c x⟩

/-- The underlying function of the canonical lift to `W \ E` is continuous. -/
theorem continuous_sdiffLiftFun
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) :
    Continuous (sdiffLiftFun h E c) := sorry

/-- The canonical morphism from a compatible cone to the cone on `W \ E`. -/
noncomputable def sdiffLift
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) :
    c.pt ⟶ (sdiffCone h E).pt :=
  TopCat.ofHom ⟨sdiffLiftFun h E c, continuous_sdiffLiftFun h E c⟩

/-- Evaluation of the canonical lift at any stage recovers that cone coordinate. -/
theorem sdiffLift_apply
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) (U : S) (x : c.pt) :
    (sdiffLift h E c x).1 = (c.π.app U x).1 := sorry

/-- The canonical lift commutes with every stage-difference projection. -/
theorem sdiffLift_fac
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S)) (U : S) :
    sdiffLift h E c ≫ (sdiffCone h E).π.app U = c.π.app U := sorry

/-- A morphism into the cone on `W \ E` is determined by its stage projections. -/
theorem sdiffLift_unique
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (c : Cone (compactOpenSdiffDiagram E S))
    (l : c.pt ⟶ (sdiffCone h E).pt)
    (hl : ∀ U : S, l ≫ (sdiffCone h E).π.app U = c.π.app U) :
    l = sdiffLift h E c := sorry

/-- The compact-open difference cone satisfies the unique-lift universal property. -/
@[stacks 0AP0 "directed compact-open difference limit presentation"]
theorem sdiffCone_limitProperty
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) :
    ∀ c : Cone (compactOpenSdiffDiagram E S),
      ∃! l : c.pt ⟶ (sdiffCone h E).pt,
        ∀ U : S, l ≫ (sdiffCone h E).π.app U = c.π.app U := sorry

/-- The canonical cone on `W \ E` is a limit of the stage-difference diagram. -/
@[stacks 0AP0 "directed compact-open difference is a limit"]
noncomputable def isLimitSdiffCone
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X) :
    IsLimit (sdiffCone h E) where
  lift := sdiffLift h E
  fac := sdiffLift_fac h E
  uniq := sdiffLift_unique h E

end IsCompactOpenDirectedIntersection
