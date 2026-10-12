/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap72.Definition_72_8_1_Modification

/-!
# Resolutions of singularities of algebraic spaces

A resolution of singularities of a Noetherian integral algebraic space is a
modification with regular source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Over a Noetherian integral target, a resolution of singularities is a modification with
regular source. -/
class IsResolution {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y) : Prop
    extends IsModification f where
  /-- The source of a resolution of singularities is regular. -/
  regularSource : IsRegular X

attribute [instance] IsResolution.regularSource

namespace IsResolution

/-- A modification with regular source is a resolution of singularities. -/
instance instOfProperties {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsModification f] [IsRegular X] : IsResolution f :=
  sorry

/-- A resolution of singularities is a modification and has regular source. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsResolution f] : IsModification f ∧ IsRegular X :=
  sorry

end IsResolution

/-- Resolution of singularities is equivalent to modification together with regularity of the
source. -/
theorem isResolution_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y) :
    IsResolution f ↔ IsModification f ∧ IsRegular X :=
  sorry

/-- The identity morphism of a Noetherian integral regular algebraic space is a resolution of
singularities. -/
instance instIsResolution_id {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [IsNoetherian Y] [IsIntegral Y] [IsRegular Y] : IsResolution (𝟙 Y) :=
  sorry

/-- A resolution of singularities of schemes over `S` induces a resolution of the associated
algebraic spaces. -/
instance instIsResolution_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) [AlgebraicGeometry.IsNoetherian V.left]
    [AlgebraicGeometry.IsIntegral V.left]
    [AlgebraicGeometry.IsResolution f.left] :
    IsResolution (ofOverMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
