module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Properties
import StacksCheckRecall

/-!
# Lemma 71.14.4

Existence of an `f`-ample invertible sheaf on a morphism of algebraic spaces
implies that the morphism is representable, quasi-compact, and separated.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u

/- Lemma 71.14.4: existence of a relatively ample invertible sheaf implies that
the morphism is representable, quasi-compact, and separated. -/
@[stacks 0D34] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.properties_of_exists :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      (∃ L : X.Modules, RelativelyAmple f L) →
        yoneda.relativelyRepresentable f ∧ QuasiCompact f ∧ Separated f)

#check (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.representable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} (L : X.Modules)
    [RelativelyAmple f L], yoneda.relativelyRepresentable f)

#check (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.quasiCompact :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [RelativelyAmple f L], QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.separated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [RelativelyAmple f L], Separated f)
