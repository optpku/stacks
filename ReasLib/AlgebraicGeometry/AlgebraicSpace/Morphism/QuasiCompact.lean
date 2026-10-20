module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RepresentableProperties

/-!
# Representable quasi-compact morphisms of algebraic spaces

For a representable morphism of algebraic spaces, quasi-compactness of all scheme
base changes is equivalent to quasi-compactness after every quasi-compact
algebraic-space base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable morphism of algebraic spaces has quasi-compact scheme base
changes if and only if its base change by every quasi-compact algebraic space
has quasi-compact source. -/
theorem quasiCompact_presheaf_iff_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f ↔
      QuasiCompact f :=
  sorry

/-- A representable morphism with quasi-compact scheme base changes is
quasi-compact as a morphism of algebraic spaces. -/
theorem quasiCompact_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.QuasiCompact :
      MorphismProperty Scheme.{u})).presheaf f) :
    QuasiCompact f :=
  sorry

/-- A representable quasi-compact morphism of algebraic spaces has
quasi-compact scheme base changes. -/
theorem quasiCompact_presheaf_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : QuasiCompact f) :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- A representable morphism has quasi-compact scheme base changes if and only
if every pullback square with a quasi-compact test algebraic space has a
quasi-compact vertex. -/
theorem quasiCompact_presheaf_iff_isQuasiCompact_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
        [IsQuasiCompact Z], IsPullback pZ pX g f → IsQuasiCompact P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
