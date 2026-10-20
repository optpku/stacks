module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Morphisms admitting relatively ample modules

A morphism of algebraic spaces admitting a relatively ample module is representable,
quasi-compact, and separated.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativelyAmple

/-- A morphism of algebraic spaces admitting a relatively ample module is representable,
quasi-compact, and separated. -/
theorem properties_of_exists {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (h : ∃ L : X.Modules, RelativelyAmple f L) :
    yoneda.relativelyRepresentable f ∧ QuasiCompact f ∧ Separated f :=
  sorry

/-- A morphism of algebraic spaces with a relatively ample module is quasi-compact. -/
theorem quasiCompact {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [RelativelyAmple f L] : QuasiCompact f :=
  (properties_of_exists f ⟨L, inferInstance⟩).2.1

/-- A morphism of algebraic spaces with a relatively ample module is separated. -/
theorem separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [RelativelyAmple f L] : Separated f :=
  (properties_of_exists f ⟨L, inferInstance⟩).2.2

end AlgebraicGeometry.AlgebraicSpace.RelativelyAmple
