/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasComparison

/-!
# Explicit descent data and their morphisms

The maps forming a descent datum are separated from the cocycle property.
Identity, composition, inversion and refinement use the given groupoid operations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite
open Functor
open CategoryTheory.CategoryOfElements

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Object and arrow maps of a `[U/R]`-descent datum, before imposing any laws. -/
structure DescentDatumData {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) where
  /-- The object maps `u_i : T_i ⟶ U`. -/
  u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left
  /-- The arrow maps `r_ij : T_i ×_T T_j ⟶ R`. -/
  r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left

/-- The cocycle property of a family of object and arrow maps. -/
def DescentDatumData.Cocycle {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (D : DescentDatumData G family) : Prop :=
    ∀ i j k
      (h :
        (ofOverMap (pr12 family i j k) ≫ D.r j k) ≫ G.s.left =
          (ofOverMap (pr01 family i j k) ≫ D.r i j) ≫ G.t.left),
      G.compArrows (ofOverMap (pr12 family i j k) ≫ D.r j k)
          (ofOverMap (pr01 family i j k) ≫ D.r i j) h =
        ofOverMap (pr02 family i j k) ≫ D.r i k

/-- A `[U/R]`-descent datum: object and arrow maps with endpoint and cocycle laws. -/
structure DescentDatum {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    extends DescentDatumData G family where
  /-- Source law: `s ∘ r_ij = u_i ∘ pr₀`. -/
  source : ∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i
  /-- Target law: `t ∘ r_ij = u_j ∘ pr₁`. -/
  target : ∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j
  /-- Cocycle law: `c ∘ (r_jk ∘ pr₁₂, r_ij ∘ pr₀₁) = r_ik ∘ pr₀₂`. -/
  cocycle : toDescentDatumData.Cocycle

namespace DescentDatum

/-- Source, target, and cocycle laws of a descent datum. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    (∀ i j, D.r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ D.u i) ∧
      (∀ i j, D.r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ D.u j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 family i j k) ≫ D.r j k) ≫ G.s.left =
              (ofOverMap (pr01 family i j k) ≫ D.r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 family i j k) ≫ D.r j k)
              (ofOverMap (pr01 family i j k) ≫ D.r i j) h =
            ofOverMap (pr02 family i j k) ≫ D.r i k :=
  ⟨D.source, D.target, D.cocycle⟩


/-- The prescribed component maps satisfy the endpoint and cocycle equations. -/
theorem trivial_laws {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    let objectMaps : ∀ i, ofOver (coverOver (identityFamily T) i) ⟶ G.U.left := fun _ ↦ ofOverMap (identityCoverHom T) ≫ u
    let r : ∀ i j, ofOver (pairOver (identityFamily T) i j) ⟶ G.R.left := fun _ _ ↦ ofOverMap (identityPairHom T) ≫ u ≫ G.e.left
    (∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 (identityFamily T) i j) ≫ objectMaps i) ∧
      (∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 (identityFamily T) i j) ≫ objectMaps j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 (identityFamily T) i j k) ≫ r j k) ≫ G.s.left =
              (ofOverMap (pr01 (identityFamily T) i j k) ≫ r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 (identityFamily T) i j k) ≫ r j k)
              (ofOverMap (pr01 (identityFamily T) i j k) ≫ r i j) h =
            ofOverMap (pr02 (identityFamily T) i j k) ≫ r i k := sorry

/-- The trivial descent datum of a morphism `T ⟶ U` on the identity covering. -/
def trivial {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    DescentDatum G (identityFamily T) where
  u := fun _ ↦ ofOverMap (identityCoverHom T) ≫ u
  r := fun _ _ ↦ ofOverMap (identityPairHom T) ≫ u ≫ G.e.left
  source := (trivial_laws G u).1
  target := (trivial_laws G u).2.1
  cocycle := (trivial_laws G u).2.2

/-- The object map of `trivial G u` is `u` after identifying the identity covering with `T`. -/
theorem trivial_u {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    (trivial G u).u PUnit.unit = ofOverMap (identityCoverHom T) ≫ u :=
  rfl


/-- The prescribed component maps satisfy the endpoint and cocycle equations. -/
theorem pullback_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    let u : ∀ i, ofOver (coverOver family' i) ⟶ G.U.left := fun j ↦ ofOverMap (coverMap α φ j) ≫ D.u (α j)
    let r : ∀ i j, ofOver (pairOver family' i j) ⟶ G.R.left := fun j j' ↦ ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j')
    (∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family' i j) ≫ u i) ∧
      (∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family' i j) ≫ u j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 family' i j k) ≫ r j k) ≫ G.s.left =
              (ofOverMap (pr01 family' i j k) ≫ r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 family' i j k) ≫ r j k)
              (ofOverMap (pr01 family' i j k) ≫ r i j) h =
            ofOverMap (pr02 family' i j k) ≫ r i k := sorry

/-- Pullback of a descent datum along a refinement `α, φ` of indexed families over `T`. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    DescentDatum G family' where
  u := fun j ↦ ofOverMap (coverMap α φ j) ≫ D.u (α j)
  r := fun j j' ↦ ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j')
  source := (pullback_laws D α φ).1
  target := (pullback_laws D α φ).2.1
  cocycle := (pullback_laws D α φ).2.2

/-- Object maps of a pulled-back descent datum are `u_{α(j)} ∘ φ_j`. -/
theorem pullback_u {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (D.pullback α φ).u j = ofOverMap (coverMap α φ j) ≫ D.u (α j) :=
  rfl

/-- Arrow maps of a pulled-back descent datum are `r_{α(j)α(j')} ∘ (φ_j × φ_{j'})`. -/
theorem pullback_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    (D.pullback α φ).r j j' = ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j') :=
  rfl

/-- A morphism of `[U/R]`-descent data over a fixed indexed family. -/
structure Hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (D D' : DescentDatum G family) where
  /-- The component arrows `r_i : T_i ⟶ R`. -/
  r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left
  /-- Source law `(α)`: `u_i = s ∘ r_i`. -/
  source : ∀ i, D.u i = r i ≫ G.s.left
  /-- Target law `(α)`: `u'_i = t ∘ r_i`. -/
  target : ∀ i, D'.u i = r i ≫ G.t.left
  /-- Compatibility `(β)`: `c ∘ (r'_ij, r_i ∘ pr₀) = c ∘ (r_j ∘ pr₁, r_ij)`. -/
  compat :
    ∀ i j
      (h₁ :
        D'.r i j ≫ G.s.left =
          (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
      (h₂ :
        (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
          D.r i j ≫ G.t.left),
      G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
        G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂

namespace Hom

/-- Source and compatibility laws of a morphism of descent data. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    (∀ i, D.u i = ψ.r i ≫ G.s.left ∧ D'.u i = ψ.r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D'.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ ψ.r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ ψ.r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ ψ.r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ ψ.r j) (D.r i j) h₂ :=
  ⟨fun i ↦ ⟨ψ.source i, ψ.target i⟩, ψ.compat⟩

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
theorem id_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    let r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left := fun i ↦ D.u i ≫ G.e.left
    (∀ i, D.u i = r i ≫ G.s.left ∧ D.u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂ := sorry

/-- Identity morphism of a descent datum, with components `e ∘ u_i`. -/
def id {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    Hom D D where
  r := fun i ↦ D.u i ≫ G.e.left
  source := fun i ↦ ((id_laws D).1 i).1
  target := fun i ↦ ((id_laws D).1 i).2
  compat := (id_laws D).2

/-- Components of the identity morphism are `e ∘ u_i`. -/
theorem id_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) (i : ι) :
    (Hom.id D).r i = D.u i ≫ G.e.left :=
  rfl

/-- Composability of component arrows of two morphisms of descent data. -/
theorem comp_composable {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') (i : ι) :
    ψ'.r i ≫ G.s.left = ψ.r i ≫ G.t.left :=
  (ψ'.source i).symm.trans (ψ.target i)

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
theorem comp_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') :
    let r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left := fun i ↦ G.compArrows (ψ'.r i) (ψ.r i) (comp_composable ψ ψ' i)
    (∀ i, D.u i = r i ≫ G.s.left ∧ D''.u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D''.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D''.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂ := sorry

/-- Composition of morphisms of descent data, with components `c ∘ (r'_i, r_i)`. -/
def comp {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') :
    Hom D D'' where
  r := fun i ↦ G.compArrows (ψ'.r i) (ψ.r i) (comp_composable ψ ψ' i)
  source := fun i ↦ ((comp_laws ψ ψ').1 i).1
  target := fun i ↦ ((comp_laws ψ ψ').1 i).2
  compat := (comp_laws ψ ψ').2

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
theorem inv_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    let r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left := fun i ↦ ψ.r i ≫ G.i.left
    (∀ i, D'.u i = r i ≫ G.s.left ∧ D.u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D'.r i j ≫ G.t.left),
        G.compArrows (D.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D'.r i j) h₂ := sorry

/-- Inverse of a morphism of descent data, with components `i ∘ r_i`. -/
def inv {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    Hom D' D where
  r := fun i ↦ ψ.r i ≫ G.i.left
  source := fun i ↦ ((inv_laws ψ).1 i).1
  target := fun i ↦ ((inv_laws ψ).1 i).2
  compat := (inv_laws ψ).2

/-- Components of the inverse morphism are `i ∘ r_i`. -/
theorem inv_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') (i : ι) :
    (ψ.inv).r i = ψ.r i ≫ G.i.left :=
  rfl

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
theorem pullback_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D')
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    let r : ∀ i, ofOver (coverOver family' i) ⟶ G.R.left := fun j ↦ ofOverMap (coverMap α φ j) ≫ ψ.r (α j)
    (∀ i, (D.pullback α φ).u i = r i ≫ G.s.left ∧ (D'.pullback α φ).u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          (D'.pullback α φ).r i j ≫ G.s.left =
            (ofOverMap (pr0 family' i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family' i j) ≫ r j) ≫ G.s.left =
            (D.pullback α φ).r i j ≫ G.t.left),
        G.compArrows ((D'.pullback α φ).r i j) (ofOverMap (pr0 family' i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family' i j) ≫ r j) ((D.pullback α φ).r i j) h₂ := sorry

/-- Pullback of a morphism of descent data along a refinement of indexed families. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D')
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    Hom (D.pullback α φ) (D'.pullback α φ) where
  r := fun j ↦ ofOverMap (coverMap α φ j) ≫ ψ.r (α j)
  source := fun i ↦ ((pullback_laws ψ α φ).1 i).1
  target := fun i ↦ ((pullback_laws ψ α φ).1 i).2
  compat := (pullback_laws ψ α φ).2

end Hom

end DescentDatum

end AlgebraicGeometry.GroupoidAlgebraicSpace
