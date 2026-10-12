/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Graph
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# The graph of a morphism of algebraic spaces

For a morphism `g : X ⟶ Y` of algebraic spaces over an algebraic space `T` over a
scheme `S`, the graph `pullback.graph x y g hg : X ⟶ pullback x y` is representable,
locally of finite type, locally quasi-finite, separated, and a monomorphism in the
sense of Definition 65.5.1. If `y : Y ⟶ T` is locally separated then it is an
immersion; if `y` is separated then it is a closed immersion; if `y` is
quasi-separated then it is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.4.6 (1): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. The graph
`pullback.graph x y g hg : X ⟶ pullback x y` of `g` is representable. -/
@[stacks 03KO]
theorem relativelyRepresentable_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    yoneda.relativelyRepresentable (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (2): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. The graph
`pullback.graph x y g hg` of `g` is locally of finite type in the sense of
Definition 65.5.1. -/
@[stacks 03KO]
theorem locallyOfFiniteType_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (3): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. The graph
`pullback.graph x y g hg` of `g` is locally quasi-finite in the sense of
Definition 65.5.1. -/
@[stacks 03KO]
theorem locallyQuasiFinite_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (4): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. The graph
`pullback.graph x y g hg` of `g` is separated in the sense of Definition 65.5.1. -/
@[stacks 03KO]
theorem isSeparated_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (5): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. The graph
`pullback.graph x y g hg` of `g` is a monomorphism in the sense of
Definition 65.5.1. -/
@[stacks 03KO]
theorem monomorphisms_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (6): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. If `Y ⟶ T` is
locally separated, then the graph `pullback.graph x y g hg` of `g` is an
immersion. -/
@[stacks 03KO]
instance isImmersion_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [LocallySeparated y] :
    IsImmersion (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (7): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. If `Y ⟶ T` is
separated, then the graph `pullback.graph x y g hg` of `g` is a closed
immersion. -/
@[stacks 03KO]
instance isClosedImmersion_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [Separated y] :
    IsClosedImmersion (pullback.graph x y g hg) :=
  sorry

/-- Lemma 67.4.6 (8): let `S` be a scheme, let `T` be an algebraic space over `S`,
and let `g : X ⟶ Y` be a morphism of algebraic spaces over `T`. If `Y ⟶ T` is
quasi-separated, then the graph `pullback.graph x y g hg` of `g` is
quasi-compact in the sense of Definition 65.5.1. -/
@[stacks 03KO]
theorem quasiCompact_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [QuasiSeparated y] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
