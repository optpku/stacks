/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_15_2_Fiber

/-!
# Support of a finite-type quasi-coherent module on an algebraic space

A finite-type quasi-coherent `𝒪_X`-module has closed support on `|X|`. At a geometric point
the support criterion is equivalent to nonvanishing of the étale stalk and of the residue-field
fiber. Pullback along any morphism of algebraic spaces preserves finite type and pulls support
back along the induced map on points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 67.15.2 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F` be a
finite type quasi-coherent `𝒪_X`-module. Then the support of `F` is closed in `|X|`. -/
@[stacks 07TZ]
theorem isClosed_moduleSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : IsClosed (moduleSupport F) :=
  sorry

/-- Lemma 67.15.2 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F` be a
finite type quasi-coherent `𝒪_X`-module. For a geometric point `xbar` lying over
`x ∈ |X|`, one has `x ∈ moduleSupport F` if and only if the étale stalk
`stalkModuleCat xbar F` is nonzero if and only if the residue-field fiber `fiber xbar F` is
nontrivial. -/
@[stacks 07TZ]
theorem mem_moduleSupport_tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (xbar : GeometricPoint X) :
    List.TFAE [xbar.image ∈ moduleSupport F, ¬ IsZero (stalkModuleCat xbar F),
      Nontrivial (fiber xbar F)] :=
  sorry

/-- A finite-type quasi-coherent `𝒪_X`-module is supported at the image of a geometric point
if and only if the residue-field fiber there is nontrivial. -/
theorem mem_moduleSupport_iff_nontrivial_fiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (xbar : GeometricPoint X) :
    xbar.image ∈ moduleSupport F ↔ Nontrivial (fiber xbar F) :=
  sorry

/-- Lemma 67.15.2 (3): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F` be a
finite type quasi-coherent `𝒪_X`-module. For any morphism of algebraic spaces `f : Y ⟶ X`,
the pullback `f* F` is of finite type. -/
@[stacks 07TZ, instance]
instance pullback_isFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : X.Modules) [F.IsFiniteType] : ((pullback f).obj F).IsFiniteType :=
  sorry

/-- Lemma 67.15.2 (4): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F` be a
finite type quasi-coherent `𝒪_X`-module. For any morphism of algebraic spaces `f : Y ⟶ X`,
one has `moduleSupport ((pullback f).obj F) = Points.map f ⁻¹' moduleSupport F`. -/
@[stacks 07TZ]
theorem moduleSupport_pullback_eq_preimage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (f : Y ⟶ X) :
    moduleSupport ((pullback f).obj F) = Points.map f ⁻¹' moduleSupport F :=
  sorry

/-- A point of `|Y|` supports `f* F` if and only if its image under `Points.map f` supports
`F`. -/
theorem mem_moduleSupport_pullback_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (f : Y ⟶ X) (y : Points Y) :
    y ∈ moduleSupport ((pullback f).obj F) ↔ Points.map f y ∈ moduleSupport F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
