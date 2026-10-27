/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Splitting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation

/-!
# Open wide subgroupoids in algebraic spaces

An open arrow subspace closed under identities, inversion, and composition defines
a groupoid on the original object space and a canonical wide inclusion.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- An open subspace `P ⊂ R` of arrows of a groupoid in algebraic spaces, together
with restricted identity, inverse, and composition maps through `P`, forming a
wide subgroupoid on the same object space. -/
structure OpenSubgroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) where
  /-- The open subspace `P ⊂ R` of arrows. -/
  P : OpenSubspace G.R.left
  /-- The restricted identity-arrow map through `P`. -/
  e' : G.U ⟶ openOver G P
  /-- The restricted inverse-arrow map on `P`. -/
  i' : openOver G P ⟶ openOver G P
  /-- The restricted composition map on `P ×_{s, U, t} P`. -/
  c' : Limits.pullback (restrictSource G P)
      (restrictTarget G P) ⟶ openOver G P
  /-- The restricted identity factors the original identity through `P ⊂ R`. -/
  identity_factor : e' ≫ openInclusion G P = G.e
  /-- The restricted inverse factors the original inverse through `P ⊂ R`. -/
  inverse_factor :
    i' ≫ openInclusion G P = openInclusion G P ≫ G.i
  /-- The restricted composition factors the original composition through `P ⊂ R`. -/
  composition_factor :
    c' ≫ openInclusion G P =
      restrictComposable G P ≫ G.c

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
    (of P e' i' c' identity_factor inverse_factor composition_factor).P = P := sorry

/-- The source of a composite is the source of its earlier arrow. -/
private theorem restrictedCompSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.c' ≫ restrictSource G H.P =
      pullback.snd (restrictSource G H.P) (restrictTarget G H.P) ≫ restrictSource G H.P := sorry

/-- The target of a composite is the target of its later arrow. -/
private theorem restrictedCompTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.c' ≫ restrictTarget G H.P =
      pullback.fst (restrictSource G H.P) (restrictTarget G H.P) ≫ restrictTarget G H.P := sorry

/-- Identity arrows have the specified source. -/
private theorem restrictedIdentitySource {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.e' ≫ (restrictSource G H.P) = 𝟙 G.U := sorry

/-- Identity arrows have the specified target. -/
private theorem restrictedIdentityTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.e' ≫ (restrictTarget G H.P) = 𝟙 G.U := sorry

/-- Inversion exchanges source with target. -/
private theorem restrictedInverseSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.i' ≫ (restrictSource G H.P) = (restrictTarget G H.P) := sorry

/-- Inversion exchanges target with source. -/
private theorem restrictedInverseTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.i' ≫ (restrictTarget G H.P) = (restrictSource G H.P) := sorry

/-- Composition is associative on every object of points over `B`. -/
private theorem restrictedAssociativity {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    ∀ {T : Over B} (a b d : T ⟶ openOver G H.P)
      (h_ab : a ≫ restrictSource G H.P = b ≫ restrictTarget G H.P)
      (h_bd : b ≫ restrictSource G H.P = d ≫ restrictTarget G H.P)
      (h_ab_d : (pullback.lift a b h_ab ≫ H.c') ≫ (restrictSource G H.P) = d ≫ (restrictTarget G H.P))
      (h_a_bd : a ≫ (restrictSource G H.P) = (pullback.lift b d h_bd ≫ H.c') ≫ (restrictTarget G H.P)),
      pullback.lift (pullback.lift a b h_ab ≫ H.c') d h_ab_d ≫ H.c' =
          pullback.lift a (pullback.lift b d h_bd ≫ H.c') h_a_bd ≫ H.c' := sorry

/-- Composing an arrow with the identity at its source does not change it. -/
private theorem restrictedRightIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    ∀ {T : Over B} (a : T ⟶ openOver G H.P)
      (h : a ≫ (restrictSource G H.P) = ((a ≫ (restrictSource G H.P)) ≫ H.e') ≫ (restrictTarget G H.P)),
      pullback.lift a ((a ≫ (restrictSource G H.P)) ≫ H.e') h ≫ H.c' = a := sorry

/-- Composing the identity at the target of an arrow with that arrow does not change it. -/
private theorem restrictedLeftIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    ∀ {T : Over B} (a : T ⟶ openOver G H.P)
      (h : ((a ≫ (restrictTarget G H.P)) ≫ H.e') ≫ (restrictSource G H.P) = a ≫ (restrictTarget G H.P)),
      pullback.lift ((a ≫ (restrictTarget G H.P)) ≫ H.e') a h ≫ H.c' = a := sorry

/-- Composing an arrow after its inverse gives the identity at its target. -/
private theorem restrictedInverseComp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    ∀ {T : Over B} (a : T ⟶ openOver G H.P)
      (h : a ≫ (restrictSource G H.P) = (a ≫ H.i') ≫ (restrictTarget G H.P)),
      pullback.lift a (a ≫ H.i') h ≫ H.c' = (a ≫ (restrictTarget G H.P)) ≫ H.e' := sorry

/-- Composing the inverse of an arrow after it gives the identity at its source. -/
private theorem restrictedCompInverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    ∀ {T : Over B} (a : T ⟶ openOver G H.P)
      (h : (a ≫ H.i') ≫ (restrictSource G H.P) = a ≫ (restrictTarget G H.P)),
      pullback.lift (a ≫ H.i') a h ≫ H.c' = (a ≫ (restrictSource G H.P)) ≫ H.e' := sorry

/-- The groupoid in algebraic spaces `(U, P, s|_P, t|_P, c)` on
`P ×_{s, U, t} P`. -/
def toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) : GroupoidAlgebraicSpace B where
  U := G.U
  R := openOver G H.P
  s := restrictSource G H.P
  t := restrictTarget G H.P
  c := H.c'
  e := H.e'
  i := H.i'
  comp_source := restrictedCompSource H
  comp_target := restrictedCompTarget H
  identity_source := restrictedIdentitySource H
  identity_target := restrictedIdentityTarget H
  inverse_source := restrictedInverseSource H
  inverse_target := restrictedInverseTarget H
  associativity := restrictedAssociativity H
  right_identity := restrictedRightIdentity H
  left_identity := restrictedLeftIdentity H
  inverse_comp := restrictedInverseComp H
  comp_inverse := restrictedCompInverse H

/-- The object space of the restricted groupoid is the original object space. -/
theorem toGroupoid_U {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) : H.toGroupoid.U = G.U := sorry

/-- The arrow space of the restricted groupoid is `openOver G H.P`. -/
theorem toGroupoid_R {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) : H.toGroupoid.R = openOver G H.P := sorry

/-- The open arrow inclusion commutes with the source maps. -/
private theorem inclusionMapSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.toGroupoid.s ≫ 𝟙 G.U = openInclusion G H.P ≫ G.s := sorry

/-- The open arrow inclusion commutes with the target maps. -/
private theorem inclusionMapTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.toGroupoid.t ≫ 𝟙 G.U = openInclusion G H.P ≫ G.t := sorry

/-- The open arrow inclusion commutes with composition. -/
private theorem inclusionMapComposition {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.toGroupoid.c ≫ openInclusion G H.P =
      composableMap (G := H.toGroupoid) (H := G) (𝟙 G.U) (openInclusion G H.P)
        (inclusionMapSource H) (inclusionMapTarget H) ≫ G.c := sorry

/-- The wide inclusion of an open subgroupoid into the ambient groupoid. -/
def hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) : Hom H.toGroupoid G where
  obj := 𝟙 G.U
  arrow := openInclusion G H.P
  map_s := inclusionMapSource H
  map_t := inclusionMapTarget H
  map_c := inclusionMapComposition H

/-- The object component of the wide inclusion is the identity on `U`. -/
theorem hom_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) : H.hom.obj = 𝟙 G.U := sorry

/-- The arrow component of the wide inclusion is the open immersion `P ⊂ R`. -/
theorem hom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) : H.hom.arrow = openInclusion G H.P := sorry

/-- An open subgroupoid is an open immersion of arrows together with identity,
inverse, and composition factorizations through `P ⊂ R`. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    AlgebraicSpace.IsOpenImmersion H.P.ι ∧
      H.e' ≫ openInclusion G H.P = G.e ∧
      H.i' ≫ openInclusion G H.P = openInclusion G H.P ≫ G.i ∧
      H.c' ≫ openInclusion G H.P = restrictComposable G H.P ≫ G.c := sorry

/-- If `s, t` are flat, then so are the restrictions `s|_P` and `t|_P`. -/
theorem flat_toGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) (h_flat : Flat G) :
    Flat H.toGroupoid := sorry

/-- If `s, t` are locally of finite presentation, then so are the restrictions
`s|_P` and `t|_P`. -/
theorem locallyOfFinitePresentation_toGroupoid {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    (h_lfp : LocallyOfFinitePresentation G) : LocallyOfFinitePresentation H.toGroupoid := sorry

end OpenSubgroupoid

end AlgebraicGeometry.GroupoidAlgebraicSpace
