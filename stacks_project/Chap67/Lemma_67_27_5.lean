/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_5_DiscreteFiber
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Locally quasi-finite morphisms of algebraic spaces and discrete field fibers

A locally finite-type morphism of algebraic spaces is locally quasi-finite
exactly when every scheme-theoretic field fiber has discrete space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.27.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. Then `f` is
locally quasi-finite if and only if for every field `k` and every morphism
`Spec(k) ⟶ Y`, the space of points of the fibre product
`X_k = Spec(k) ×_Y X` is discrete. -/
@[stacks 06RW]
theorem locallyQuasiFinite_iff_discreteFieldFibers
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ discreteFieldFibers f :=
  sorry

namespace LocallyQuasiFinite

/-- A locally-of-finite-type morphism of algebraic spaces with discrete field
fibers is locally quasi-finite. -/
theorem of_discreteFieldFibers {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] (h : discreteFieldFibers f) :
    LocallyQuasiFinite f :=
  sorry

end LocallyQuasiFinite

namespace discreteFieldFibers

/-- A locally-of-finite-type locally quasi-finite morphism of algebraic spaces
has discrete field fibers. -/
theorem of_locallyQuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    discreteFieldFibers f :=
  sorry

end discreteFieldFibers

end AlgebraicGeometry.AlgebraicSpace
