module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The local ring map `𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}` is an isomorphism when it is so
on some pair of schematic open neighbourhoods of `x` and `f(x)`. -/
def IsIsoStalkMapAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V) (u : U.left),
    IsOpenImmersion ιX ∧ IsOpenImmersion ιY ∧ ofOverMap φ ≫ ιY = ιX ≫ f ∧
      Points.map ιX (ofOver.pointsEquiv U u) = x ∧ IsIso (φ.left.stalkMap u)

/-- Unfold the schematic-neighbourhood characterization of a stalk isomorphism
at a point. -/
theorem isIsoStalkMapAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    IsIsoStalkMapAt f x ↔
      ∃ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V) (u : U.left),
        IsOpenImmersion ιX ∧ IsOpenImmersion ιY ∧ ofOverMap φ ≫ ιY = ιX ≫ f ∧
          Points.map ιX (ofOver.pointsEquiv U u) = x ∧ IsIso (φ.left.stalkMap u) :=
  sorry

namespace IsIsoStalkMapAt

/-- A commuting square of schematic open neighbourhoods whose scheme-level stalk
map is an isomorphism witnesses `IsIsoStalkMapAt`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    {U V : Over S} {ιX : ofOver U ⟶ X} {ιY : ofOver V ⟶ Y} {φ : U ⟶ V} {u : U.left}
    [IsOpenImmersion ιX] [IsOpenImmersion ιY] (hcomm : ofOverMap φ ≫ ιY = ιX ≫ f)
    (hx : Points.map ιX (ofOver.pointsEquiv U u) = x) [IsIso (φ.left.stalkMap u)] :
    IsIsoStalkMapAt f x :=
  sorry

/-- On the schematic loci of the source and target, a stalk isomorphism at `x`
is independent of the choice of schematic open neighbourhoods. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    IsIsoStalkMapAt f x ↔
      x ∈ schematicLocusPoints X ∧ Points.map f x ∈ schematicLocusPoints Y ∧
        ∀ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V) (u : U.left),
          IsOpenImmersion ιX → IsOpenImmersion ιY → ofOverMap φ ≫ ιY = ιX ≫ f →
            Points.map ιX (ofOver.pointsEquiv U u) = x → IsIso (φ.left.stalkMap u) :=
  sorry

end IsIsoStalkMapAt

end AlgebraicGeometry.AlgebraicSpace
