/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.«94_9_8_1_Comparison»
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Testing immersions of algebraic stacks on one fppf covering

A morphism of algebraic stacks is an open (resp. closed) immersion if and only
if the 2-fibre product against one surjective, flat, locally of finite
presentation algebraic-space covering is an algebraic space whose projection
is an open (resp. closed) immersion of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace OpenImmersion

/-- Lemma 100.9.4 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`W` be an algebraic space and let `g : W.toGroupoids ⟶ Y` be surjective, flat,
and locally of finite presentation. Then `f` is an open immersion if and only
if `V = W ×_Y X` is an algebraic space and `V ⟶ W` is an open immersion of
algebraic spaces, equivalently if there exist `V` and `v : V ⟶ W` representing
the 2-fibre product via `RepresentsTwoFibreProductOnSpace` (corresponding to
`TwoFibreProduct.fst g f`) with `AlgebraicSpace.IsOpenImmersion v`. -/
@[stacks 0503]
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    OpenImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsOpenImmersion v :=
  sorry

/-- If `v : V ⟶ W` represents the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f`, then `f` is an open immersion if and
only if `v` is an open immersion of algebraic spaces. -/
theorem iff_of_representing {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    OpenImmersion f ↔ AlgebraicSpace.IsOpenImmersion v :=
  sorry

/-- If a morphism of algebraic spaces representing the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an open immersion, then `f` is an open
immersion. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsOpenImmersion v → OpenImmersion f :=
  sorry

/-- If `f` is an open immersion, then a morphism of algebraic spaces representing
the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is an open
immersion. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsOpenImmersion v :=
  sorry

/-- If `f` is an open immersion, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_apex {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

end OpenImmersion

namespace ClosedImmersion

/-- Lemma 100.9.4 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`W` be an algebraic space and let `g : W.toGroupoids ⟶ Y` be surjective, flat,
and locally of finite presentation. Then `f` is a closed immersion if and only
if `V = W ×_Y X` is an algebraic space and `V ⟶ W` is a closed immersion of
algebraic spaces, equivalently if there exist `V` and `v : V ⟶ W` representing
the 2-fibre product via `RepresentsTwoFibreProductOnSpace` (corresponding to
`TwoFibreProduct.fst g f`) with `AlgebraicSpace.IsClosedImmersion v`. -/
@[stacks 0503]
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    ClosedImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsClosedImmersion v :=
  sorry

/-- If `v : V ⟶ W` represents the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f`, then `f` is a closed immersion if and
only if `v` is a closed immersion of algebraic spaces. -/
theorem iff_of_representing {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    ClosedImmersion f ↔ AlgebraicSpace.IsClosedImmersion v :=
  sorry

/-- If a morphism of algebraic spaces representing the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is a closed immersion, then `f` is a closed
immersion. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsClosedImmersion v → ClosedImmersion f :=
  sorry

/-- If `f` is a closed immersion, then a morphism of algebraic spaces representing
the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is a closed
immersion. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsClosedImmersion v :=
  sorry

/-- If `f` is a closed immersion, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_apex {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [ClosedImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

end ClosedImmersion

end AlgebraicGeometry.Groupoids.Hom
