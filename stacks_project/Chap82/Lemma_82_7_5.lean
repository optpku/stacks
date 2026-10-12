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
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction

/-!
# Closures of images of locally finite closed families

In the good setup of Situation 82.2.1, a quasi-compact morphism over `B` sends a
locally finite family of closed subsets of the source point space to a locally
finite family of closures of images in the target point space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.7.5: In Situation 82.2.1 let `X, Y / B` be good. Let `f : X ⟶ Y` be a
morphism over `B`. Assume `f` is quasi-compact, and `{T i}` is a locally finite
collection of closed subsets of `Points X`. Then `{closure (Points.map f '' T i)}`
is a locally finite collection of closed subsets of `Points Y`. -/
@[stacks 0ENZ]
theorem locallyFinite_closure_image {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiCompact f] {I : Type v} (T : I → Closeds (Points X))
    (hT : LocallyFinite (fun i ↦ (T i : Set (Points X)))) :
    LocallyFinite (fun i ↦ closure (Points.map f '' (T i : Set (Points X)))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
