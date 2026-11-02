/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
open CategoryTheory.Limits
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
  rfl

/-- A point of `B` lies in `unramifiedBaseLocus G` if and only if `G.X.hom` is
unramified at the identity-section image of that point. -/
theorem mem_unramifiedBaseLocus {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (b : Points B) :
    b ∈ (unramifiedBaseLocus G).pointsSet ↔
      UnramifiedAt G.X.hom (Points.map η[G.X].left b) :=
  by
    rw [unramifiedBaseLocus, OpenSubspace.inverseImage_pointsSet]
    exact Unramified.mem_sourceLocus G.X.hom (Points.map η[G.X].left b)

/-- The points of `unramifiedBaseLocus G` are the preimage of the unramified
source locus along the identity section. -/
theorem unramifiedBaseLocus_eq_sourceLocus_preimage {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (unramifiedBaseLocus G).pointsSet =
      Points.map η[G.X].left ⁻¹' (Unramified.sourceLocus G.X.hom).pointsSet :=
  OpenSubspace.inverseImage_pointsSet _ _

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
  ⟨rfl, unramifiedBaseLocus_ι G, (unramifiedBaseLocus G).isOpenImmersion,
    mem_unramifiedBaseLocus G⟩

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
  rfl

/-- A point of `B` lies in `locallyQuasiFiniteBaseLocus G` if and only if
`G.X.hom` is quasi-finite at the identity-section image of that point. -/
theorem mem_locallyQuasiFiniteBaseLocus {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (b : Points B) :
    b ∈ (locallyQuasiFiniteBaseLocus G).pointsSet ↔
      QuasiFiniteAt G.X.hom (Points.map η[G.X].left b) :=
  by
    rw [locallyQuasiFiniteBaseLocus, OpenSubspace.inverseImage_pointsSet]
    exact mem_quasiFiniteLocus_iff_quasiFiniteAt G.X.hom (Points.map η[G.X].left b)

/-- The points of `locallyQuasiFiniteBaseLocus G` are the preimage of the
quasi-finite locus along the identity section. -/
theorem locallyQuasiFiniteBaseLocus_eq_quasiFiniteLocus_preimage
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (locallyQuasiFiniteBaseLocus G).pointsSet =
      Points.map η[G.X].left ⁻¹' (quasiFiniteLocus G.X.hom).pointsSet :=
  OpenSubspace.inverseImage_pointsSet _ _

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
  ⟨rfl, locallyQuasiFiniteBaseLocus_ι G, (locallyQuasiFiniteBaseLocus G).isOpenImmersion,
    mem_locallyQuasiFiniteBaseLocus G⟩

private theorem baseChange_one_fst {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (g : B' ⟶ B) :
    η[(baseChange G g).X].left ≫ pullback.fst G.X.hom g =
      g ≫ η[G.X].left := by
  change ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
    ((Over.pullback g).map η[G.X]).left) ≫ _ = _
  rw [Category.assoc]
  change (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
    pullback.lift (pullback.fst (𝟙 B) g ≫ η[G.X].left)
      (pullback.snd (𝟙 B) g) _ ≫ pullback.fst G.X.hom g = _
  rw [pullback.lift_fst]
  have hfst : pullback.fst (𝟙 B) g = pullback.snd (𝟙 B) g ≫ g := by
    simpa using (pullback.condition (f := 𝟙 B) (g := g))
  have hε : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
      pullback.snd (𝟙 B) g = 𝟙 B' :=
    (Functor.LaxMonoidal.ε (Over.pullback g)).w
  have hεfst : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
      pullback.fst (𝟙 B) g = g := by
    rw [hfst]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ g) hε).trans (Category.id_comp g))
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫ η[G.X].left) hεfst)

private theorem unramifiedAt_baseChange_one_iff {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (b : Points B') :
    UnramifiedAt (baseChange G g).X.hom (Points.map η[(baseChange G g).X].left b) ↔
      UnramifiedAt G.X.hom (Points.map η[G.X].left (Points.map g b)) := by
  change UnramifiedAt (pullback.snd G.X.hom g)
      (Points.map η[(baseChange G g).X].left b) ↔ _
  have h := Unramified.unramifiedAt_iff_of_isPullback
      (pullback.fst G.X.hom g) (pullback.snd G.X.hom g) G.X.hom g
      (IsPullback.of_hasPullback G.X.hom g)
      (Points.map η[(baseChange G g).X].left b)
  convert h using 1
  rw [← Points.map_comp, ← Points.map_comp]
  change UnramifiedAt G.X.hom (Points.map (g ≫ η[G.X].left) b) ↔
    UnramifiedAt G.X.hom
      (Points.map (η[(baseChange G g).X].left ≫ pullback.fst G.X.hom g) b)
  rw [baseChange_one_fst G g]
  rfl

private theorem quasiFiniteAt_baseChange_one_iff {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (b : Points B') :
    QuasiFiniteAt (baseChange G g).X.hom (Points.map η[(baseChange G g).X].left b) ↔
      QuasiFiniteAt G.X.hom (Points.map η[G.X].left (Points.map g b)) := by
  change QuasiFiniteAt (pullback.snd G.X.hom g)
      (Points.map η[(baseChange G g).X].left b) ↔ _
  have h := quasiFiniteAt_iff_of_isPullback
      (pullback.fst G.X.hom g) (pullback.snd G.X.hom g) G.X.hom g
      (IsPullback.of_hasPullback G.X.hom g)
      (Points.map η[(baseChange G g).X].left b)
  convert h using 1
  rw [← Points.map_comp, ← Points.map_comp]
  change QuasiFiniteAt G.X.hom (Points.map (g ≫ η[G.X].left) b) ↔
    QuasiFiniteAt G.X.hom
      (Points.map (η[(baseChange G g).X].left ≫ pullback.fst G.X.hom g) b)
  rw [baseChange_one_fst G g]
  rfl

/-- The restriction of a group algebraic space to its unramified base locus is
unramified. -/
instance instUnramified_unramifiedBaseLocus {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.Unramified
      (baseChange G (unramifiedBaseLocus G).ι).X.hom :=
  by
    apply (unramified_iff_unramifiedAt_one _).mpr
    intro b
    apply (unramifiedAt_baseChange_one_iff G (unramifiedBaseLocus G).ι b).mpr
    exact (mem_unramifiedBaseLocus G _).mp ⟨b, rfl⟩

/-- The restriction of a group algebraic space to its locally quasi-finite base
locus is locally quasi-finite. -/
instance instLocallyQuasiFinite_locallyQuasiFiniteBaseLocus {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite
      (baseChange G (locallyQuasiFiniteBaseLocus G).ι).X.hom :=
  by
    apply (locallyQuasiFinite_iff_quasiFiniteAt_one _).mpr
    intro b
    apply (quasiFiniteAt_baseChange_one_iff G (locallyQuasiFiniteBaseLocus G).ι b).mpr
    exact (mem_locallyQuasiFiniteBaseLocus G _).mp ⟨b, rfl⟩

/-- Every open subspace over which a locally finite-type group algebraic space is
unramified is contained in its unramified base locus. -/
theorem unramifiedBaseLocus_maximal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (V : OpenSubspace B)
    [AlgebraicSpace.Unramified (baseChange G V.ι).X.hom] :
    V.pointsSet ⊆ (unramifiedBaseLocus G).pointsSet :=
  by
    rintro _ ⟨b, rfl⟩
    apply (mem_unramifiedBaseLocus G _).mpr
    apply (unramifiedAt_baseChange_one_iff G V.ι b).mp
    exact (unramified_iff_unramifiedAt_one (baseChange G V.ι)).mp inferInstance b

/-- The unramified base locus of a locally finite-type group algebraic space
commutes with arbitrary base change. -/
theorem unramifiedBaseLocus_eq_preimage {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (unramifiedBaseLocus (baseChange G g)).pointsSet =
      Points.map g ⁻¹' (unramifiedBaseLocus G).pointsSet :=
  by
    ext b
    simp only [Set.mem_preimage, mem_unramifiedBaseLocus]
    exact unramifiedAt_baseChange_one_iff G g b

/-- Every open subspace over which a locally finite-type group algebraic space is
locally quasi-finite is contained in its locally quasi-finite base locus. -/
theorem locallyQuasiFiniteBaseLocus_maximal {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (V : OpenSubspace B)
    [AlgebraicSpace.LocallyQuasiFinite (baseChange G V.ι).X.hom] :
    V.pointsSet ⊆ (locallyQuasiFiniteBaseLocus G).pointsSet :=
  by
    rintro _ ⟨b, rfl⟩
    apply (mem_locallyQuasiFiniteBaseLocus G _).mpr
    apply (quasiFiniteAt_baseChange_one_iff G V.ι b).mp
    exact (locallyQuasiFinite_iff_quasiFiniteAt_one (baseChange G V.ι)).mp inferInstance b

/-- The locally quasi-finite base locus of a locally finite-type group algebraic
space commutes with arbitrary base change. -/
theorem locallyQuasiFiniteBaseLocus_eq_preimage {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (locallyQuasiFiniteBaseLocus (baseChange G g)).pointsSet =
      Points.map g ⁻¹' (locallyQuasiFiniteBaseLocus G).pointsSet :=
  by
    ext b
    simp only [Set.mem_preimage, mem_locallyQuasiFiniteBaseLocus]
    exact quasiFiniteAt_baseChange_one_iff G g b

end AlgebraicGeometry.GroupAlgebraicSpace
