/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_34_7_QuasiFiniteLocus
public import stacks_project.Chap67.Lemma_67_38_10_SourceLocus
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage
public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap78.Lemma_78_5_2

/-!
# Unramified and locally quasi-finite base loci of group algebraic spaces

If `G` is a group algebraic space locally of finite type over `B`, the maximal
open of `B` over which `G` is unramified (resp. locally quasi-finite) is the
inverse image of the unramified source locus (resp. quasi-finite locus) along
the identity section `η[G.X].left`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Base change of a locally of finite type group algebraic space remains
locally of finite type. -/
instance instLocallyOfFiniteType_grpOverPullback {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyOfFiniteType (grpOverPullback G g).X.hom :=
  sorry

/-- The maximal open subspace of `B` over which a locally of finite type group
algebraic space is unramified, as the inverse image of
`Unramified.sourceLocus G.X.hom` along the identity section. -/
def unramifiedBaseLocus {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    OpenSubspace B :=
  (Unramified.sourceLocus G.X.hom).inverseImage η[G.X].left

/-- The inclusion of `unramifiedBaseLocus G` is the open inverse image of the
unramified source locus along `η[G.X].left`. -/
theorem unramifiedBaseLocus_ι {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (unramifiedBaseLocus G).ι =
      openInverseImageι η[G.X].left (Unramified.sourceLocus G.X.hom).ι :=
  sorry

/-- A point of `B` lies in `unramifiedBaseLocus G` if and only if `G.X.hom` is
unramified at the identity-section image of that point. -/
theorem mem_unramifiedBaseLocus {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (b : Points B) :
    b ∈ (unramifiedBaseLocus G).pointsSet ↔
      UnramifiedAt G.X.hom (Points.map η[G.X].left b) :=
  sorry

/-- The points of `unramifiedBaseLocus G` are the preimage of the unramified
source locus along the identity section. -/
theorem unramifiedBaseLocus_eq_sourceLocus_preimage {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (unramifiedBaseLocus G).pointsSet =
      Points.map η[G.X].left ⁻¹' (Unramified.sourceLocus G.X.hom).pointsSet :=
  sorry

/-- `unramifiedBaseLocus G` is the identity-section inverse image of the
unramified source locus, included by an open immersion, and its points are
exactly those at which `G.X.hom` is unramified along `η[G.X].left`. -/
theorem unramifiedBaseLocus_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    unramifiedBaseLocus G =
        (Unramified.sourceLocus G.X.hom).inverseImage η[G.X].left ∧
      (unramifiedBaseLocus G).ι =
        openInverseImageι η[G.X].left (Unramified.sourceLocus G.X.hom).ι ∧
      AlgebraicSpace.IsOpenImmersion (unramifiedBaseLocus G).ι ∧
      ∀ b : Points B,
        b ∈ (unramifiedBaseLocus G).pointsSet ↔
          UnramifiedAt G.X.hom (Points.map η[G.X].left b) :=
  sorry

/-- The maximal open subspace of `B` over which a locally of finite type group
algebraic space is locally quasi-finite, as the inverse image of
`quasiFiniteLocus G.X.hom` along the identity section. -/
def locallyQuasiFiniteBaseLocus {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    OpenSubspace B :=
  (quasiFiniteLocus G.X.hom).inverseImage η[G.X].left

/-- The inclusion of `locallyQuasiFiniteBaseLocus G` is the open inverse image
of the quasi-finite locus along `η[G.X].left`. -/
theorem locallyQuasiFiniteBaseLocus_ι {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (locallyQuasiFiniteBaseLocus G).ι =
      openInverseImageι η[G.X].left (quasiFiniteLocus G.X.hom).ι :=
  sorry

/-- A point of `B` lies in `locallyQuasiFiniteBaseLocus G` if and only if
`G.X.hom` is quasi-finite at the identity-section image of that point. -/
theorem mem_locallyQuasiFiniteBaseLocus {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (b : Points B) :
    b ∈ (locallyQuasiFiniteBaseLocus G).pointsSet ↔
      QuasiFiniteAt G.X.hom (Points.map η[G.X].left b) :=
  sorry

/-- The points of `locallyQuasiFiniteBaseLocus G` are the preimage of the
quasi-finite locus along the identity section. -/
theorem locallyQuasiFiniteBaseLocus_eq_quasiFiniteLocus_preimage
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (locallyQuasiFiniteBaseLocus G).pointsSet =
      Points.map η[G.X].left ⁻¹' (quasiFiniteLocus G.X.hom).pointsSet :=
  sorry

/-- `locallyQuasiFiniteBaseLocus G` is the identity-section inverse image of
the quasi-finite locus, included by an open immersion, and its points are
exactly those at which `G.X.hom` is quasi-finite along `η[G.X].left`. -/
theorem locallyQuasiFiniteBaseLocus_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    locallyQuasiFiniteBaseLocus G =
        (quasiFiniteLocus G.X.hom).inverseImage η[G.X].left ∧
      (locallyQuasiFiniteBaseLocus G).ι =
        openInverseImageι η[G.X].left (quasiFiniteLocus G.X.hom).ι ∧
      AlgebraicSpace.IsOpenImmersion (locallyQuasiFiniteBaseLocus G).ι ∧
      ∀ b : Points B,
        b ∈ (locallyQuasiFiniteBaseLocus G).pointsSet ↔
          QuasiFiniteAt G.X.hom (Points.map η[G.X].left b) :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
