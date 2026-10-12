/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction

/-!
# Inverse images of locally finite closed families

In the good setup of Situation 82.2.1, inverse images along a morphism over `B`
preserve locally finite families of closed subsets of the underlying spaces of
points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.9.2: In Situation 82.2.1 let `X, Y / B` be good. Let `f : X ⟶ Y` be a
morphism over `B`. If `T` is a locally finite collection of closed subsets of
`Points Y`, then `(T i).preimage (Points.continuous_map f)` is a locally finite
collection of closed subsets of `Points X`. -/
@[stacks 0EP6]
theorem locallyFinite_preimage {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (hf : f ≫ pY = pX)
    {I : Type v} (T : I → Closeds (Points Y))
    (hT : LocallyFinite (fun i ↦ (T i : Set (Points Y)))) :
    LocallyFinite
      (fun i ↦ ((T i).preimage (Points.continuous_map f) : Set (Points X))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
