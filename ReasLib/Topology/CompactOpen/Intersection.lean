module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed intersections of compact open subspaces

This module owns the topology- and category-theory-only presentation of a subset as a nonempty
downward-directed intersection of compact open subsets. Spectrality is deliberately absent: it is
added by `ReasLib.Topology.Spectral.CompactOpenIntersection`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/-- A nonempty downward-directed family of compact open subsets whose intersection is `W`. -/
@[stacks 0A31 "compact-open directed intersections"]
structure IsCompactOpenDirectedIntersection
    (W : Set X) (S : Set (CompactOpens X)) : Prop where
  /-- The family of stages is nonempty. -/
  nonempty : S.Nonempty
  /-- The displayed subset is the intersection of all stages. -/
  eq_iInter : W = ⋂ U ∈ S, (U : Set X)
  /-- Any two stages admit a common smaller stage in the family. -/
  directed : DirectedOn (· ≥ ·) S

/-- The defining conditions of a compact-open directed-intersection presentation. -/
theorem isCompactOpenDirectedIntersection_iff
    {W : Set X} {S : Set (CompactOpens X)} :
    IsCompactOpenDirectedIntersection W S ↔
      S.Nonempty ∧ W = ⋂ U ∈ S, (U : Set X) ∧ DirectedOn (· ≥ ·) S := sorry

namespace IsCompactOpenDirectedIntersection

/-- A point in the intersection belongs to every displayed compact-open stage. -/
theorem mem
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    {x : X} (hx : x ∈ W) {U : CompactOpens X} (hU : U ∈ S) :
    x ∈ (U : Set X) := sorry

/-- A nonempty downward-directed compact-open presentation gives a cofiltered stage category. -/
theorem isCofiltered
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) :
    IsCofiltered S := sorry

end IsCompactOpenDirectedIntersection

/-- The map from a family of compact opens to their underlying open subsets is monotone. -/
theorem compactOpenFamilyToOpens_monotone (S : Set (CompactOpens X)) :
    Monotone (fun U : S ↦ U.1.toOpens) := sorry

/-- A compact-open family viewed as a monotone family of open subsets. -/
def compactOpenFamilyToOpens (S : Set (CompactOpens X)) : S →o Opens X :=
  ⟨fun U ↦ U.1.toOpens, compactOpenFamilyToOpens_monotone S⟩

/-- Evaluating the monotone compact-open family returns the underlying open subset. -/
@[simp]
theorem compactOpenFamilyToOpens_apply {S : Set (CompactOpens X)} (U : S) :
    compactOpenFamilyToOpens S U = U.1.toOpens := sorry

/-- The `TopCat` diagram of open subspaces associated to a compact-open family. -/
@[stacks 0A31 "compact-open intersection diagram"]
def compactOpenIntersectionDiagram (S : Set (CompactOpens X)) : S ⥤ TopCat :=
  (compactOpenFamilyToOpens S).toFunctor ⋙ Opens.toTopCat (TopCat.of X)

namespace IsCompactOpenDirectedIntersection

/-- The canonical map from the intersection subtype to a displayed compact-open stage is
continuous. -/
theorem continuous_coneApp
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (U : S) :
    Continuous (fun x : W ↦ (⟨x.1, h.mem x.2 U.2⟩ : U.1)) := sorry

/-- The canonical map from the intersection subtype to one compact-open stage. -/
def coneApp
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (U : S) :
    TopCat.of W ⟶ (compactOpenIntersectionDiagram S).obj U :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, h.mem x.2 U.2⟩, continuous_coneApp h U⟩

/-- A stage projection from the intersection preserves the ambient point. -/
theorem coneApp_apply
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (U : S) (x : W) :
    (coneApp h U x).1 = x.1 := sorry

/-- The stage maps from the intersection subtype are natural in the compact-open stage. -/
theorem cone_naturality
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    {U V : S} (f : U ⟶ V) :
    ((Functor.const S).obj (TopCat.of W)).map f ≫ coneApp h V =
      coneApp h U ≫ (compactOpenIntersectionDiagram S).map f := sorry

/-- The canonical cone from a compact-open intersection subtype to its diagram of stages. -/
@[stacks 0A31 "compact-open intersection cone"]
def cone
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) :
    Cone (compactOpenIntersectionDiagram S) where
  pt := TopCat.of W
  π :=
    { app := coneApp h
      naturality := fun _ _ f ↦ cone_naturality h f }

/-- The ambient value of the canonical lift, computed at an arbitrary chosen stage. The
choice-independent characterization is `liftValue_eq`. -/
noncomputable def liftValue
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) (x : c.pt) : X :=
  (c.π.app (⟨h.nonempty.choose, h.nonempty.choose_spec⟩ : S) x).1

/-- The ambient value of the canonical lift agrees with evaluation at every displayed stage. -/
theorem liftValue_eq
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) (U : S) (x : c.pt) :
    liftValue h c x = (c.π.app U x).1 := sorry

/-- The chosen-stage value of a compatible cone belongs to the displayed intersection. -/
theorem liftValue_mem
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) (x : c.pt) :
    liftValue h c x ∈ W := sorry

/-- The underlying function of the canonical lift from a compatible cone to the intersection. -/
noncomputable def liftFun
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) : c.pt → W :=
  fun x ↦ ⟨liftValue h c x, liftValue_mem h c x⟩

/-- The underlying function of the canonical intersection lift is continuous. -/
theorem continuous_liftFun
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) :
    Continuous (liftFun h c) := sorry

/-- The canonical lift from a compatible cone to the compact-open intersection cone. -/
noncomputable def lift
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) :
    c.pt ⟶ (cone h).pt :=
  TopCat.ofHom ⟨liftFun h c, continuous_liftFun h c⟩

/-- Evaluation of the canonical lift at any stage recovers that cone coordinate. -/
theorem lift_apply
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) (U : S) (x : c.pt) :
    (lift h c x).1 = (c.π.app U x).1 := sorry

/-- The canonical intersection lift commutes with every stage projection. -/
theorem lift_fac
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S)) (U : S) :
    lift h c ≫ (cone h).π.app U = c.π.app U := sorry

/-- A morphism into the intersection cone is determined by all its stage projections. -/
theorem lift_unique
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S)
    (c : Cone (compactOpenIntersectionDiagram S))
    (l : c.pt ⟶ (cone h).pt)
    (hl : ∀ U : S, l ≫ (cone h).π.app U = c.π.app U) :
    l = lift h c := sorry

/-- The canonical compact-open intersection cone satisfies the unique-lift universal property.
This statement is topology- and category-theory-only, so it has no spectral-space assumption. -/
@[stacks 0A31 "inverse-limit presentation"]
theorem cone_limitProperty
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) :
    ∀ c : Cone (compactOpenIntersectionDiagram S),
      ∃! l : c.pt ⟶ (cone h).pt,
        ∀ U : S, l ≫ (cone h).π.app U = c.π.app U := sorry

/-- The compact-open intersection cone is a limit cone independently of spectrality; spectrality
is needed only to deduce that its cone point is spectral. -/
@[stacks 0A31 "compact-open intersection is a limit"]
noncomputable def isLimitCone
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) :
    IsLimit (cone h) where
  lift := lift h
  fac := lift_fac h
  uniq := lift_unique h

end IsCompactOpenDirectedIntersection
