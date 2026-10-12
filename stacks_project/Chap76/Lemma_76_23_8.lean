/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_23_7_FiniteFree

/-!
# Openness of the finite-free étale locus

If `f : X ⟶ Y` is locally of finite presentation and `F` is a finitely presented
`𝒪_X`-module flat over `Y`, the locus of points at which `F` is finite free in an
étale neighbourhood is open in `Points X`, and it is stable under arbitrary base
change of `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `X` at which a quasi-coherent module `F` is finite free in
an étale neighbourhood. -/
def finiteFreeEtaleLocus {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    Set (Points X) :=
  {x | finiteFreeEtaleAt F x}

/-- Membership in `finiteFreeEtaleLocus F` is finite-freeness of `F` in an étale
neighbourhood of the point. -/
theorem mem_finiteFreeEtaleLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (x : Points X) :
    x ∈ finiteFreeEtaleLocus F ↔ finiteFreeEtaleAt F x :=
  sorry

/-- Lemma 76.23.8 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite presentation. Let `F` be a finitely
presented `𝒪_X`-module flat over `Y`. Then the set of points of `|X|` at which `F`
is free in an étale neighbourhood is open in `|X|`. -/
@[stacks 0CZT]
theorem isOpen_finiteFreeEtaleLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (h_flat : flatOver F f) : IsOpen (finiteFreeEtaleLocus F) :=
  sorry

/-- Lemma 76.23.8 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite presentation. Let `F` be a finitely
presented `𝒪_X`-module flat over `Y`. For a morphism `g : Y' ⟶ Y` of algebraic
spaces over `S`, the locus of points at which
`(pullback (pullback.fst f g)).obj F` is free in an étale neighbourhood is the
inverse image of `finiteFreeEtaleLocus F` under `Points.map (pullback.fst f g)`. -/
@[stacks 0CZT]
theorem finiteFreeEtaleLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) (g : Y' ⟶ Y) :
    finiteFreeEtaleLocus ((pullback (pullback.fst f g)).obj F) =
      Points.map (pullback.fst f g) ⁻¹' finiteFreeEtaleLocus F :=
  sorry

/-- A point of `Points (pullback f g)` lies in the finite-free étale locus of the
pulled-back module if and only if its image under `Points.map (pullback.fst f g)`
lies in `finiteFreeEtaleLocus F`. -/
theorem mem_finiteFreeEtaleLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) (g : Y' ⟶ Y)
    (x' : Points (Limits.pullback f g)) :
    x' ∈ finiteFreeEtaleLocus ((pullback (pullback.fst f g)).obj F) ↔
      Points.map (pullback.fst f g) x' ∈ finiteFreeEtaleLocus F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
