module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Resolution
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

/- Over a Noetherian integral target, a resolution of singularities is a modification with
regular source. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsResolution :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X], (X ⟶ Y) → Prop)

/- A modification with regular source is a resolution of singularities. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsResolution.instOfProperties :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsModification f] [IsRegular X], IsResolution f)

/- A resolution of singularities is a modification and has regular source. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsResolution.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsResolution f], IsModification f ∧ IsRegular X)

/- Resolution of singularities is equivalent to modification together with regularity of the
source. -/
#check (AlgebraicGeometry.AlgebraicSpace.isResolution_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y),
    IsResolution f ↔ IsModification f ∧ IsRegular X)

/- The identity morphism of a Noetherian integral regular algebraic space is a resolution of
singularities. -/
#check (AlgebraicGeometry.AlgebraicSpace.instIsResolution_id :
  ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [IsNoetherian Y] [IsIntegral Y] [IsRegular Y], IsResolution (𝟙 Y))

/- A resolution of singularities of schemes over `S` induces a resolution of the associated
algebraic spaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.instIsResolution_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) [AlgebraicGeometry.IsNoetherian V.left]
    [AlgebraicGeometry.IsIntegral V.left]
    [AlgebraicGeometry.IsResolution f.left], IsResolution (ofOverMap f))

end AlgebraicGeometry.AlgebraicSpace
