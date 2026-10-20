module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackComparison
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Graph

/-!
# Geometric properties of graph morphisms

The graph of a morphism of algebraic spaces over a common base is representable,
locally of finite type, locally quasi-finite, separated, and a monomorphism.
Separation properties of the target over the base imply immersion and
quasi-compactness properties of the graph.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The graph of a morphism of algebraic spaces over a common base is representable. -/
theorem relativelyRepresentable_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    yoneda.relativelyRepresentable (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces over a common base is representably
locally of finite type. -/
theorem locallyOfFiniteType_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces over a common base is representably
locally of finite type and locally quasi-finite. -/
theorem locallyQuasiFinite_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces over a common base is representably
separated. -/
theorem isSeparated_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces over a common base is a representable
monomorphism. -/
theorem monomorphisms_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces whose target is locally separated
over the base is an immersion. -/
instance isImmersion_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [LocallySeparated y] :
    IsImmersion (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces whose target is separated over the
base is a closed immersion. -/
instance isClosedImmersion_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [Separated y] :
    IsClosedImmersion (pullback.graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic spaces whose target is quasi-separated
over the base is representably quasi-compact. -/
theorem quasiCompact_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [QuasiSeparated y] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
