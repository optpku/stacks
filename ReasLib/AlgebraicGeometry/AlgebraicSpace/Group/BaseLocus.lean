module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.LocalProperties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus

/-!
# Unramified and locally quasi-finite base loci of group algebraic spaces

For a group algebraic space locally of finite type, the identity-section
inverse images of the unramified and quasi-finite source loci are the maximal
base opens over which the structure morphism has the corresponding property.
Both base loci commute with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

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

/-- The restriction of a group algebraic space to its unramified base locus is
unramified. -/
instance instUnramified_unramifiedBaseLocus {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.Unramified
      (baseChange G (unramifiedBaseLocus G).ι).X.hom :=
  sorry

/-- The restriction of a group algebraic space to its locally quasi-finite base
locus is locally quasi-finite. -/
instance instLocallyQuasiFinite_locallyQuasiFiniteBaseLocus {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite
      (baseChange G (locallyQuasiFiniteBaseLocus G).ι).X.hom :=
  sorry

/-- Every open subspace over which a locally finite-type group algebraic space is
unramified is contained in its unramified base locus. -/
theorem unramifiedBaseLocus_maximal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (V : OpenSubspace B)
    [AlgebraicSpace.Unramified (baseChange G V.ι).X.hom] :
    V.pointsSet ⊆ (unramifiedBaseLocus G).pointsSet :=
  sorry

/-- The unramified base locus of a locally finite-type group algebraic space
commutes with arbitrary base change. -/
theorem unramifiedBaseLocus_eq_preimage {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (unramifiedBaseLocus (baseChange G g)).pointsSet =
      Points.map g ⁻¹' (unramifiedBaseLocus G).pointsSet :=
  sorry

/-- Every open subspace over which a locally finite-type group algebraic space is
locally quasi-finite is contained in its locally quasi-finite base locus. -/
theorem locallyQuasiFiniteBaseLocus_maximal {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (V : OpenSubspace B)
    [AlgebraicSpace.LocallyQuasiFinite (baseChange G V.ι).X.hom] :
    V.pointsSet ⊆ (locallyQuasiFiniteBaseLocus G).pointsSet :=
  sorry

/-- The locally quasi-finite base locus of a locally finite-type group algebraic
space commutes with arbitrary base change. -/
theorem locallyQuasiFiniteBaseLocus_eq_preimage {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (locallyQuasiFiniteBaseLocus (baseChange G g)).pointsSet =
      Points.map g ⁻¹' (locallyQuasiFiniteBaseLocus G).pointsSet :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
