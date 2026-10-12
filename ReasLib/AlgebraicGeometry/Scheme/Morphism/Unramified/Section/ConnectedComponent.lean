/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Section
public import ReasLib.Topology.ConnectedComponents.Set

/-!
# Connected components arising from sections of unramified morphisms
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

/-- A section of an unramified separated morphism to a connected scheme is an open immersion,
and its range is the unique connected component on which the morphism restricts to an
isomorphism. -/
theorem isOpenImmersion_and_existsUnique_connectedComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConnectedSpace Y] [Unramified f] [IsSeparated f] (s : SplitEpi f) :
    IsOpenImmersion s.section_ ∧
      ∃! C : ConnectedComponents X,
        Set.range s.section_ = C.set ∧
          ∃ U : X.Opens, (U : Set X) = C.set ∧ IsIso (U.ι ≫ f) := sorry

/-- The connected component containing the value of a section over a connected scheme is
independent of the chosen point of the base. -/
theorem componentAt_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [ConnectedSpace Y]
    (s : SplitEpi f) (y y' : Y) :
    (s.section_ y : ConnectedComponents X) = (s.section_ y' : ConnectedComponents X) := sorry

/-- Evaluating sections of an unramified separated morphism at a point of the connected base is
injective, and its range consists exactly of the source components on which the morphism is an
isomorphism. -/
theorem componentAt_injective_and_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConnectedSpace Y] [Unramified f] [IsSeparated f] (y : Y) :
    Function.Injective (fun s : SplitEpi f ↦ (s.section_ y : ConnectedComponents X)) ∧
      Set.range (fun s : SplitEpi f ↦ (s.section_ y : ConnectedComponents X)) =
        {C | ∃ U : X.Opens, (U : Set X) = C.set ∧ IsIso (U.ι ≫ f)} := sorry

/-- Two sections of an unramified separated morphism to a connected scheme are equal if their
ranges contain a common point. -/
theorem eq_of_mem_section_ranges {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConnectedSpace Y] [Unramified f] [IsSeparated f] (x : X) (s t : SplitEpi f)
    (hs : x ∈ Set.range s.section_) (ht : x ∈ Set.range t.section_) : s = t := sorry

end AlgebraicGeometry.Scheme.Hom.Section
