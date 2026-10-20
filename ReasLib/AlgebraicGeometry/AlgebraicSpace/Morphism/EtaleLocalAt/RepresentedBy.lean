module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.RepresentedBy

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- For a scheme-morphism property `P` étale local on source-and-target, the associated
germ property holds at a point of an algebraic-space morphism exactly when `etaleLocal P`
holds on an open neighbourhood of that point. -/
theorem existsEtaleSquareAt_iff_existsOpenEtaleLocal {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    existsEtaleSquareAt (representedBy P) f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          etaleLocal P (i ≫ f) :=
  sorry

/-- For a scheme-morphism property `P` étale local on source-and-target, an algebraic-space
morphism satisfies `etaleLocal P` exactly when the associated represented germ property
holds at every point of its source. -/
theorem etaleLocal_iff_forall_existsEtaleSquareAt {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocal P f ↔
      ∀ x : Points X, existsEtaleSquareAt (representedBy P) f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
