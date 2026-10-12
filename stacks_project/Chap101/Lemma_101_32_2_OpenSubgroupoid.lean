/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_9_8_QuotientMap

/-!
# Open subgroupoids of groupoids in algebraic spaces

An open subspace `P ⊂ R` of the arrow space of a groupoid in algebraic spaces,
together with restricted identity, inverse, and composition maps through `P`,
is an open wide subgroupoid on the same object space. The induced map of
quotient stacks is `quotientHom : [U / P] ⟶ [U / R]`.

The open-arrow constructions match the finite-open-subgroupoid helpers, but live
here so `[U / P] ⟶ [U / R]` can be `Hom.quotientStackHom` of the wide inclusion.
Importing `Groupoid.Splitting` alongside that quotient-stack map is currently
blocked by incompatible algebraic-space points modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace OpenSubgroupoid

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

/-- Comparison of composable pairs `P ×_{s, U, t} P → R ×_{s, U, t} R` induced by
`P ⊂ R`. -/
def restrictComposable {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    Limits.pullback (restrictSource G P) (restrictTarget G P) ⟶ Limits.pullback G.s G.t :=
  Limits.pullback.map (restrictSource G P) (restrictTarget G P) G.s G.t
    (openInclusion G P) (openInclusion G P) (𝟙 G.U)
    (Category.comp_id _) (Category.comp_id _)

/-- The first projection of `restrictComposable G P` is `openInclusion G P` after
the first projection. -/
theorem restrictComposable_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : OpenSubspace G.R.left) :
    restrictComposable G P ≫ Limits.pullback.fst G.s G.t =
      Limits.pullback.fst (restrictSource G P) (restrictTarget G P) ≫ openInclusion G P :=
  sorry

end OpenSubgroupoid

/-- An open subspace `P ⊂ R` of arrows of a groupoid in algebraic spaces, together
with restricted identity, inverse, and composition maps through `P`, forming a
wide subgroupoid on the same object space. -/
structure OpenSubgroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) where
  /-- The open subspace `P ⊂ R` of arrows. -/
  P : OpenSubspace G.R.left
  /-- The restricted identity-arrow map through `P`. -/
  e' : G.U ⟶ OpenSubgroupoid.openOver G P
  /-- The restricted inverse-arrow map on `P`. -/
  i' : OpenSubgroupoid.openOver G P ⟶ OpenSubgroupoid.openOver G P
  /-- The restricted composition map on `P ×_{s, U, t} P`. -/
  c' : Limits.pullback (OpenSubgroupoid.restrictSource G P)
      (OpenSubgroupoid.restrictTarget G P) ⟶ OpenSubgroupoid.openOver G P
  /-- The restricted identity factors the original identity through `P ⊂ R`. -/
  identity_factor : e' ≫ OpenSubgroupoid.openInclusion G P = G.e
  /-- The restricted inverse factors the original inverse through `P ⊂ R`. -/
  inverse_factor :
    i' ≫ OpenSubgroupoid.openInclusion G P = OpenSubgroupoid.openInclusion G P ≫ G.i
  /-- The restricted composition factors the original composition through `P ⊂ R`. -/
  composition_factor :
    c' ≫ OpenSubgroupoid.openInclusion G P =
      OpenSubgroupoid.restrictComposable G P ≫ G.c

namespace OpenSubgroupoid

/-- Build an open subgroupoid from an open subspace of arrows, restricted
structure maps, and the three factorization identities. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (P : OpenSubspace G.R.left) (e' : G.U ⟶ openOver G P)
    (i' : openOver G P ⟶ openOver G P)
    (c' : Limits.pullback (restrictSource G P) (restrictTarget G P) ⟶ openOver G P)
    (identity_factor : e' ≫ openInclusion G P = G.e)
    (inverse_factor : i' ≫ openInclusion G P = openInclusion G P ≫ G.i)
    (composition_factor : c' ≫ openInclusion G P = restrictComposable G P ≫ G.c) :
    OpenSubgroupoid G where
  P := P
  e' := e'
  i' := i'
  c' := c'
  identity_factor := identity_factor
  inverse_factor := inverse_factor
  composition_factor := composition_factor

/-- The open subspace of arrows of `OpenSubgroupoid.of` is the given `P`. -/
theorem of_P {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (P : OpenSubspace G.R.left) (e' : G.U ⟶ openOver G P)
    (i' : openOver G P ⟶ openOver G P)
    (c' : Limits.pullback (restrictSource G P) (restrictTarget G P) ⟶ openOver G P)
    (identity_factor : e' ≫ openInclusion G P = G.e)
    (inverse_factor : i' ≫ openInclusion G P = openInclusion G P ≫ G.i)
    (composition_factor : c' ≫ openInclusion G P = restrictComposable G P ≫ G.c) :
    (of P e' i' c' identity_factor inverse_factor composition_factor).P = P :=
  sorry

/-- The groupoid in algebraic spaces `(U, P, s|_P, t|_P, c)` on
`P ×_{s, U, t} P`. -/
def toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : GroupoidAlgebraicSpace B where
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
    (H : OpenSubgroupoid G) : H.toGroupoid.U = G.U :=
  sorry

/-- The arrow space of the restricted groupoid is `openOver G H.P`. -/
theorem toGroupoid_R {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : H.toGroupoid.R = openOver G H.P :=
  sorry

/-- The wide inclusion of an open subgroupoid into the ambient groupoid. -/
def hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : Hom H.toGroupoid G where
  obj := 𝟙 G.U
  arrow := openInclusion G H.P
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of the wide inclusion is the identity on `U`. -/
theorem hom_obj {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : H.hom.obj = 𝟙 G.U :=
  sorry

/-- The arrow component of the wide inclusion is the open immersion `P ⊂ R`. -/
theorem hom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : H.hom.arrow = openInclusion G H.P :=
  sorry

/-- The induced morphism `[U / P] ⟶ [U / R]` of quotient stacks. -/
def quotientHom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : H.toGroupoid.quotientStack ⟶ G.quotientStack :=
  Hom.quotientStackHom H.hom

/-- `quotientHom` is `Hom.quotientStackHom` of the wide inclusion. -/
theorem quotientHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.quotientHom = Hom.quotientStackHom H.hom :=
  sorry

/-- An open subgroupoid is an open immersion of arrows together with identity,
inverse, and composition factorizations through `P ⊂ R`. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) :
    AlgebraicSpace.IsOpenImmersion H.P.ι ∧
      H.e' ≫ openInclusion G H.P = G.e ∧
      H.i' ≫ openInclusion G H.P = openInclusion G H.P ≫ G.i ∧
      H.c' ≫ openInclusion G H.P = restrictComposable G H.P ≫ G.c :=
  sorry

/-- If `s, t` are flat, then so are the restrictions `s|_P` and `t|_P`. -/
instance instFlat_toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) [Flat G] :
    Flat H.toGroupoid :=
  sorry

/-- If `s, t` are locally of finite presentation, then so are the restrictions
`s|_P` and `t|_P`. -/
instance instLocallyOfFinitePresentation_toGroupoid {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    [LocallyOfFinitePresentation G] : LocallyOfFinitePresentation H.toGroupoid :=
  sorry

end OpenSubgroupoid

end AlgebraicGeometry.GroupoidAlgebraicSpace
