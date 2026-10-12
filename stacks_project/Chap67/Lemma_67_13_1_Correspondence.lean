/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

/-!
# Closed subspaces and quasi-coherent ideal sheaves

A closed subspace of an algebraic space determines the kernel of
`𝒪_X ⟶ ι_* 𝒪_Z`. Conversely, a quasi-coherent ideal sheaf cuts out a closed
subspace via `subscheme`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The kernel of `𝒪_X ⟶ ι_* 𝒪_Z`, as an ideal subobject of `𝒪_X`. -/
noncomputable abbrev idealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : IdealSubobject X :=
  Hom.idealSheafSubobject Z.ι

/-- The ideal sheaf of a closed subspace is the kernel subobject of its inclusion. -/
theorem idealSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    Z.idealSheaf = Hom.idealSheafSubobject Z.ι :=
  sorry

/-- The closed subspace of `X` cut out by a quasi-coherent ideal sheaf. -/
noncomputable def ofQuasiCoherentIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] : ClosedSubspace X :=
  ofι (subschemeι I)

/-- The inclusion of the closed subspace cut out by `I` is `subschemeι I`. -/
theorem ofQuasiCoherentIdeal_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (ofQuasiCoherentIdeal I).ι = subschemeι I :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
