/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer

/-!
# Finite open subgroupoids and splittings of groupoids in algebraic spaces

An open subspace `P ⊂ R` of the arrow space of a groupoid in algebraic spaces,
together with restricted identity, inverse, and composition maps through `P` and
finiteness of `s|_P` and `t|_P`, is a finite open subgroupoid on the same object
space. Pointwise fibre, stabilizer, and identity-arrow conditions distinguish
strong splittings, splittings, and quasi-splittings over a point `u ∈ |U|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The open subspace `P ⊂ R` viewed as an object of `Over B` with the same
structure map as the arrow space. -/
def openOver {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left) : Over B :=
  Over.mk (P.ι ≫ G.R.hom)

/-- The structure morphism of `openOver G P` is `P.ι ≫ G.R.hom`. -/
theorem openOver_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left) : (openOver G P).hom = P.ι ≫ G.R.hom :=
  sorry

/-- The open immersion `P ⊂ R` as a morphism of objects over `B`. -/
def openInclusion {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left) : openOver G P ⟶ G.R :=
  Over.homMk P.ι rfl

/-- The underlying morphism of algebraic spaces of `openInclusion G P` is `P.ι`. -/
theorem openInclusion_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    (openInclusion G P).left = P.ι :=
  sorry

/-- The restriction `s|_P` of the source map to an open subspace of arrows. -/
def restrictSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left) : openOver G P ⟶ G.U :=
  openInclusion G P ≫ G.s

/-- The underlying morphism of `restrictSource G P` is `P.ι ≫ G.s.left`. -/
theorem restrictSource_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    (restrictSource G P).left = P.ι ≫ G.s.left :=
  sorry

/-- The restriction `t|_P` of the target map to an open subspace of arrows. -/
def restrictTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left) : openOver G P ⟶ G.U :=
  openInclusion G P ≫ G.t

/-- The underlying morphism of `restrictTarget G P` is `P.ι ≫ G.t.left`. -/
theorem restrictTarget_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    (restrictTarget G P).left = P.ι ≫ G.t.left :=
  sorry

/-- Comparison of composable pairs `P ×_{s,U,t} P → R ×_{s,U,t} R` induced by
`P ⊂ R`. -/
def restrictComposable {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    pullback (restrictSource G P) (restrictTarget G P) ⟶ pullback G.s G.t :=
  pullback.map (restrictSource G P) (restrictTarget G P) G.s G.t
    (openInclusion G P) (openInclusion G P) (𝟙 G.U)
    (Category.comp_id _) (Category.comp_id _)

/-- The first projection of `restrictComposable G P` is `openInclusion G P` after
the first projection. -/
theorem restrictComposable_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    restrictComposable G P ≫ pullback.fst G.s G.t =
      pullback.fst (restrictSource G P) (restrictTarget G P) ≫ openInclusion G P :=
  sorry

/-- The set `{r ∈ |R| : s(r) = u ∧ t(r) = u}` of arrows based at a point of `|U|`. -/
def sourceTargetFiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) : Set (Points G.R.left) :=
  {r | Points.map G.s.left r = u ∧ Points.map G.t.left r = u}

/-- Membership in the equalizer fibre of source and target at `u`. -/
theorem sourceTargetFiber_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) (r : Points G.R.left) :
    r ∈ sourceTargetFiber G u ↔
      Points.map G.s.left r = u ∧ Points.map G.t.left r = u :=
  sorry

/-- The image in `|R|` of the fibre of the stabilizer `G → U` over `u`. -/
def stabilizerFiberPoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) : Set (Points G.R.left) :=
  Set.image (Points.map G.toPreRelation.stabilizerToArrows.left)
    (setOf fun g : Points G.stabilizer.X.left.left ↦
      Points.map G.stabilizer.X.hom.left g = u)

/-- A point of `|R|` lies in the stabilizer fibre over `u` exactly when it is the
image of a stabilizer point mapping to `u`. -/
theorem mem_stabilizerFiberPoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) (r : Points G.R.left) :
    r ∈ stabilizerFiberPoints G u ↔
      ∃ g : Points G.stabilizer.X.left.left,
        Points.map G.stabilizer.X.hom.left g = u ∧
          Points.map G.toPreRelation.stabilizerToArrows.left g = r :=
  sorry

/-- An open subspace of arrows which is a wide subgroupoid with finite source and
target, on the same object space. -/
structure FiniteOpenSubgroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) where
  /-- The open subspace `P ⊂ R` of arrows. -/
  P : OpenSubspace G.R.left
  /-- The restricted identity-arrow map through `P`. -/
  e' : G.U ⟶ openOver G P
  /-- The restricted inverse-arrow map on `P`. -/
  i' : openOver G P ⟶ openOver G P
  /-- The restricted composition map on `P ×_{s,U,t} P`. -/
  c' : pullback (restrictSource G P) (restrictTarget G P) ⟶ openOver G P
  /-- The restricted identity factors the original identity through `P ⊂ R`. -/
  identity_factor : e' ≫ openInclusion G P = G.e
  /-- The restricted inverse factors the original inverse through `P ⊂ R`. -/
  inverse_factor : i' ≫ openInclusion G P = openInclusion G P ≫ G.i
  /-- The restricted composition factors the original composition through `P ⊂ R`. -/
  composition_factor : c' ≫ openInclusion G P = restrictComposable G P ≫ G.c
  /-- The restricted source `s|_P` is finite. -/
  finite_s : AlgebraicSpace.IsFinite (P.ι ≫ G.s.left)
  /-- The restricted target `t|_P` is finite. -/
  finite_t : AlgebraicSpace.IsFinite (P.ι ≫ G.t.left)

namespace FiniteOpenSubgroupoid

/-- Build a finite open subgroupoid from an open subspace of arrows, restricted
structure maps, factorization identities, and finiteness of source and target. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (P : OpenSubspace G.R.left) (e' : G.U ⟶ openOver G P)
    (i' : openOver G P ⟶ openOver G P)
    (c' : pullback (restrictSource G P) (restrictTarget G P) ⟶ openOver G P)
    (identity_factor : e' ≫ openInclusion G P = G.e)
    (inverse_factor : i' ≫ openInclusion G P = openInclusion G P ≫ G.i)
    (composition_factor : c' ≫ openInclusion G P = restrictComposable G P ≫ G.c)
    (finite_s : AlgebraicSpace.IsFinite (P.ι ≫ G.s.left))
    (finite_t : AlgebraicSpace.IsFinite (P.ι ≫ G.t.left)) :
    FiniteOpenSubgroupoid G where
  P := P
  e' := e'
  i' := i'
  c' := c'
  identity_factor := identity_factor
  inverse_factor := inverse_factor
  composition_factor := composition_factor
  finite_s := finite_s
  finite_t := finite_t

/-- The open subspace of arrows of `FiniteOpenSubgroupoid.of` is the given `P`. -/
theorem of_P {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (P : OpenSubspace G.R.left) (e' : G.U ⟶ openOver G P)
    (i' : openOver G P ⟶ openOver G P)
    (c' : pullback (restrictSource G P) (restrictTarget G P) ⟶ openOver G P)
    (identity_factor : e' ≫ openInclusion G P = G.e)
    (inverse_factor : i' ≫ openInclusion G P = openInclusion G P ≫ G.i)
    (composition_factor : c' ≫ openInclusion G P = restrictComposable G P ≫ G.c)
    (finite_s : AlgebraicSpace.IsFinite (P.ι ≫ G.s.left))
    (finite_t : AlgebraicSpace.IsFinite (P.ι ≫ G.t.left)) :
    (of P e' i' c' identity_factor inverse_factor composition_factor finite_s
        finite_t).P = P :=
  sorry

/-- The groupoid in algebraic spaces `(U, P, s|_P, t|_P, c|_{P ×_{s,U,t} P})`. -/
def toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : GroupoidAlgebraicSpace B where
  U := G.U
  R := openOver G H.P
  s := restrictSource G H.P
  t := restrictTarget G H.P
  c := H.c'
  e := H.e'
  i := H.i'
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of the restricted groupoid is the original object space. -/
theorem toGroupoid_U {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : H.toGroupoid.U = G.U :=
  sorry

/-- The arrow space of the restricted groupoid is `openOver G H.P`. -/
theorem toGroupoid_R {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : H.toGroupoid.R = openOver G H.P :=
  sorry

/-- The wide inclusion of a finite open subgroupoid into the ambient groupoid. -/
def hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : Hom H.toGroupoid G where
  obj := 𝟙 G.U
  arrow := openInclusion G H.P
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of the wide inclusion is the identity on `U`. -/
theorem hom_obj {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : H.hom.obj = 𝟙 G.U :=
  sorry

/-- The arrow component of the wide inclusion is the open immersion `P ⊂ R`. -/
theorem hom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : H.hom.arrow = openInclusion G H.P :=
  sorry

/-- A finite open subgroupoid is an open immersion of arrows with finite restricted
source and target, together with identity, inverse, and composition factorizations. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) :
    AlgebraicSpace.IsOpenImmersion H.P.ι ∧
      AlgebraicSpace.IsFinite (H.P.ι ≫ G.s.left) ∧
      AlgebraicSpace.IsFinite (H.P.ι ≫ G.t.left) ∧
      H.e' ≫ openInclusion G H.P = G.e ∧
      H.i' ≫ openInclusion G H.P = openInclusion G H.P ≫ G.i ∧
      H.c' ≫ openInclusion G H.P = restrictComposable G H.P ≫ G.c :=
  sorry

/-- The restricted source of a finite open subgroupoid is finite. -/
theorem isFinite_s {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : AlgebraicSpace.IsFinite (H.P.ι ≫ G.s.left) :=
  sorry

/-- The restricted target of a finite open subgroupoid is finite. -/
theorem isFinite_t {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : FiniteOpenSubgroupoid G) : AlgebraicSpace.IsFinite (H.P.ι ≫ G.t.left) :=
  sorry

end FiniteOpenSubgroupoid

/-- A strong splitting of `R` over `u` is a finite open subgroupoid containing
every arrow based at `u`. -/
structure StrongSplitting {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left)
    extends FiniteOpenSubgroupoid G where
  /-- The equalizer fibre `{r ∈ |R| : s(r) = u ∧ t(r) = u}` is contained in `|P|`. -/
  fiber_subset : sourceTargetFiber G u ⊆ Set.range (Points.map P.ι)

namespace StrongSplitting

/-- Build a strong splitting from a finite open subgroupoid containing the
source-target fibre over `u`. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {u : Points G.U.left} (H : FiniteOpenSubgroupoid G)
    (h : sourceTargetFiber G u ⊆ Set.range (Points.map H.P.ι)) : StrongSplitting G u where
  toFiniteOpenSubgroupoid := H
  fiber_subset := h

/-- The underlying finite open subgroupoid of `StrongSplitting.of` is the given
datum. -/
theorem of_toFiniteOpenSubgroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {u : Points G.U.left} (H : FiniteOpenSubgroupoid G)
    (h : sourceTargetFiber G u ⊆ Set.range (Points.map H.P.ι)) :
    (of H h).toFiniteOpenSubgroupoid = H :=
  sorry

/-- A strong splitting contains the source-target fibre over `u`. -/
theorem sourceTargetFiber_subset {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {u : Points G.U.left} (H : StrongSplitting G u) :
    sourceTargetFiber G u ⊆ Set.range (Points.map H.P.ι) :=
  sorry

end StrongSplitting

/-- A splitting of `R` over `u` is a finite open subgroupoid containing the
stabilizer fibre over `u`. -/
structure Splitting {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left)
    extends FiniteOpenSubgroupoid G where
  /-- The stabilizer fibre `{g ∈ |G| : g maps to u}` is contained in `|P|`. -/
  stabilizer_subset : stabilizerFiberPoints G u ⊆ Set.range (Points.map P.ι)

namespace Splitting

/-- Build a splitting from a finite open subgroupoid containing the stabilizer
fibre over `u`. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {u : Points G.U.left} (H : FiniteOpenSubgroupoid G)
    (h : stabilizerFiberPoints G u ⊆ Set.range (Points.map H.P.ι)) : Splitting G u where
  toFiniteOpenSubgroupoid := H
  stabilizer_subset := h

/-- The underlying finite open subgroupoid of `Splitting.of` is the given datum. -/
theorem of_toFiniteOpenSubgroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {u : Points G.U.left} (H : FiniteOpenSubgroupoid G)
    (h : stabilizerFiberPoints G u ⊆ Set.range (Points.map H.P.ι)) :
    (of H h).toFiniteOpenSubgroupoid = H :=
  sorry

/-- A splitting contains the stabilizer fibre over `u`. -/
theorem stabilizerFiberPoints_subset {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {u : Points G.U.left} (H : Splitting G u) :
    stabilizerFiberPoints G u ⊆ Set.range (Points.map H.P.ι) :=
  sorry

end Splitting

/-- A quasi-splitting of `R` over `u` is a finite open subgroupoid containing the
identity arrow at `u`. -/
structure QuasiSplitting {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left)
    extends FiniteOpenSubgroupoid G where
  /-- The identity arrow `e(u)` lies in `|P|`. -/
  identity_mem : Points.map G.e.left u ∈ Set.range (Points.map P.ι)

namespace QuasiSplitting

/-- Build a quasi-splitting from a finite open subgroupoid containing the identity
arrow at `u`. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {u : Points G.U.left} (H : FiniteOpenSubgroupoid G)
    (h : Points.map G.e.left u ∈ Set.range (Points.map H.P.ι)) : QuasiSplitting G u where
  toFiniteOpenSubgroupoid := H
  identity_mem := h

/-- The underlying finite open subgroupoid of `QuasiSplitting.of` is the given
datum. -/
theorem of_toFiniteOpenSubgroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {u : Points G.U.left} (H : FiniteOpenSubgroupoid G)
    (h : Points.map G.e.left u ∈ Set.range (Points.map H.P.ι)) :
    (of H h).toFiniteOpenSubgroupoid = H :=
  sorry

/-- A quasi-splitting contains the identity arrow `e(u)`. -/
theorem identityArrow_mem {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {u : Points G.U.left} (H : QuasiSplitting G u) :
    Points.map G.e.left u ∈ Set.range (Points.map H.P.ι) :=
  sorry

end QuasiSplitting

/-- The arrow space `R` is strongly split over `u` when a strong splitting exists. -/
def IsStronglySplitOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) : Prop :=
  Nonempty (StrongSplitting G u)

/-- Strong splitting over `u` is equivalent to the existence of a finite open
subgroupoid containing the source-target fibre at `u`. -/
theorem isStronglySplitOver_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) :
    IsStronglySplitOver G u ↔
      ∃ H : FiniteOpenSubgroupoid G, sourceTargetFiber G u ⊆ Set.range (Points.map H.P.ι) :=
  sorry

/-- The arrow space `R` is split over `u` when a splitting exists. -/
def IsSplitOver {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (u : Points G.U.left) : Prop :=
  Nonempty (Splitting G u)

/-- Splitting over `u` is equivalent to the existence of a finite open subgroupoid
containing the stabilizer fibre at `u`. -/
theorem isSplitOver_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) :
    IsSplitOver G u ↔
      ∃ H : FiniteOpenSubgroupoid G, stabilizerFiberPoints G u ⊆ Set.range (Points.map H.P.ι) :=
  sorry

/-- The arrow space `R` is quasi-split over `u` when a quasi-splitting exists. -/
def IsQuasiSplitOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) : Prop :=
  Nonempty (QuasiSplitting G u)

/-- Quasi-splitting over `u` is equivalent to the existence of a finite open
subgroupoid containing the identity arrow at `u`. -/
theorem isQuasiSplitOver_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left) :
    IsQuasiSplitOver G u ↔
      ∃ H : FiniteOpenSubgroupoid G, Points.map G.e.left u ∈ Set.range (Points.map H.P.ι) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
