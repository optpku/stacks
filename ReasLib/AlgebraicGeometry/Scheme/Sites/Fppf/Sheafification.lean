/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf

/-!
# Fppf sheafification in the universe of the presheaf

Presented affine covers give a double-plus construction valued in the original universe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfSheafification

/-- A finitely presented algebra over the sections of an open of a scheme, encoded by a
finite generating set and a finite list of polynomial relations. -/
structure PresentedAlgebra {X : Scheme.{u}} (U : X.Opens) where
  /-- The number of polynomial generators. -/
  nvars : ℕ
  /-- The number of relations. -/
  nrels : ℕ
  /-- The relations as polynomials in `nvars` variables over `Γ(X, U)`. -/
  rels : Fin nrels → MvPolynomial (Fin nvars) Γ(X, U)

/-- The trivial finitely presented algebra `Γ(X, U)` itself. -/
def PresentedAlgebra.trivial {X : Scheme.{u}} (U : X.Opens) : PresentedAlgebra U where
  nvars := 0
  nrels := 0
  rels := fun i ↦ i.elim0

/-- Base change of a presented algebra along a ring map on sections. -/
def PresentedAlgebra.map {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) : PresentedAlgebra V where
  nvars := A.nvars
  nrels := A.nrels
  rels i := MvPolynomial.map φ.hom (A.rels i)

/-- The Type-`u` coefficient ring of a presented algebra over an open. -/
def presentedRing {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    CommRingCat.{u} :=
  .of (MvPolynomial (Fin A.nvars) Γ(X, U) ⧸ Ideal.span (Set.range A.rels))

/-- `presentedRing A` is the quotient of the polynomial ring by the presented relations. -/
theorem presentedRing_eq {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    presentedRing A =
      .of (MvPolynomial (Fin A.nvars) Γ(X, U) ⧸ Ideal.span (Set.range A.rels)) :=
  rfl

/-- The spectrum of a presented algebra over an open. -/
def presentedSpec {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) : Scheme.{u} :=
  Spec (presentedRing A)

/-- `presentedSpec A` is `Spec` of `presentedRing A`. -/
theorem presentedSpec_eq {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    presentedSpec A = Spec (presentedRing A) :=
  rfl

/-- The ring map `Γ(X, U) ⟶ presentedRing A` sending variables to the generators. -/
def presentedRingHomFromGamma {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    CommRingCat.of Γ(X, U) ⟶ presentedRing A :=
  CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span (Set.range A.rels))).comp
      (MvPolynomial.C : Γ(X, U) →+* MvPolynomial (Fin A.nvars) Γ(X, U)))

/-- The morphism `Spec (presentedRing A) ⟶ Spec Γ(X, U)` induced by the structure map. -/
def presentedToGamma {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    presentedSpec A ⟶ Spec (CommRingCat.of Γ(X, U)) :=
  Spec.map (presentedRingHomFromGamma A)

/-- The morphism `Spec (presentedRing A) ⟶ X` through an affine open `U`. -/
def presentedHom {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (A : PresentedAlgebra U) : presentedSpec A ⟶ X :=
  presentedToGamma A ≫ Spec.map (CommRingCat.ofHom (RingHom.id Γ(X, U))) ≫ hU.fromSpec

/-- `presentedHom hU A` factors as the structure map of the presented algebra followed by
`hU.fromSpec`. -/
theorem presentedHom_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (A : PresentedAlgebra U) :
    presentedHom hU A =
      presentedToGamma A ≫ Spec.map (CommRingCat.ofHom (RingHom.id Γ(X, U))) ≫
        hU.fromSpec :=
  rfl

/-- The presented spectrum as a scheme over `S`. -/
def presentedOver {S : Scheme.{u}} (T : Over S) {U : T.left.Opens}
    (hU : IsAffineOpen U) (A : PresentedAlgebra U) : Over S :=
  Over.mk (presentedHom hU A ≫ T.hom)

/-- The structure morphism `presentedOver T hU A ⟶ T`. -/
def presentedOverHom {S : Scheme.{u}} (T : Over S) {U : T.left.Opens}
    (hU : IsAffineOpen U) (A : PresentedAlgebra U) :
    presentedOver T hU A ⟶ T :=
  Over.homMk (presentedHom hU A) rfl

/-- Coefficient base change sends the ideal of relations into the kernel of the
map to the quotient by the base-changed relations. -/
theorem presentedRingHom_relations {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) :
    Ideal.span (Set.range A.rels) ≤ RingHom.ker
      ((Ideal.Quotient.mk (Ideal.span (Set.range (A.map φ).rels))).comp
        (MvPolynomial.map φ.hom)) :=
  sorry

/-- The ring map on presented algebras induced by a map of coefficient rings. -/
def presentedRingHom {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) :
    presentedRing A ⟶ presentedRing (A.map φ) :=
  CommRingCat.ofHom
    (Ideal.Quotient.lift _
      ((Ideal.Quotient.mk (Ideal.span (Set.range (A.map φ).rels))).comp
        (MvPolynomial.map φ.hom)) (presentedRingHom_relations A φ))

/-- The morphism of presented spectra induced by a map of coefficient rings. -/
def presentedSpecMap {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) :
    presentedSpec (A.map φ) ⟶ presentedSpec A :=
  Spec.map (presentedRingHom A φ)

/-- The map of presented spectra commutes with the structure morphisms to the base. -/
theorem presentedOverMap_w {S : Scheme.{u}} {T T' : Over S} (f : T' ⟶ T)
    {U : T.left.Opens} (hU : IsAffineOpen U) (A : PresentedAlgebra U)
    {V : T'.left.Opens} (hV : IsAffineOpen V) (hle : V ≤ f.left ⁻¹ᵁ U) :
    presentedSpecMap A (f.left.appLE U V hle) ≫ (presentedOver T hU A).hom =
      (presentedOver T' hV (A.map (f.left.appLE U V hle))).hom :=
  sorry

/-- The morphism over `S` from a base-changed presented covering piece to the original piece. -/
def presentedOverMap {S : Scheme.{u}} {T T' : Over S} (f : T' ⟶ T)
    {U : T.left.Opens} (hU : IsAffineOpen U) (A : PresentedAlgebra U)
    {V : T'.left.Opens} (hV : IsAffineOpen V) (hle : V ≤ f.left ⁻¹ᵁ U) :
    presentedOver T' hV (A.map (f.left.appLE U V hle)) ⟶ presentedOver T hU A :=
  Over.homMk (presentedSpecMap A (f.left.appLE U V hle))
    (presentedOverMap_w f hU A hV hle)

/-- An fppf matching family of sections of a Type-`u` presheaf: a jointly surjective family of
finitely presented flat morphisms `Spec A_U ⟶ T` from presented algebras over affine opens of
`T`, together with compatible sections of `F`. -/
structure FppfMatching {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) where
  /-- The affine opens of `T` equipped with presented algebras. -/
  pieces : Set (Σ U : T.left.Opens, PresentedAlgebra U)
  /-- Each supporting open is affine. -/
  isAffine : ∀ p ∈ pieces, IsAffineOpen p.1
  /-- Each presented structure morphism is flat. -/
  isFlat : ∀ p (hp : p ∈ pieces), AlgebraicGeometry.Flat (presentedHom (isAffine p hp) p.2)
  /-- Each presented structure morphism is locally of finite presentation. -/
  isLocallyOfFinitePresentation :
    ∀ p (hp : p ∈ pieces),
      AlgebraicGeometry.LocallyOfFinitePresentation (presentedHom (isAffine p hp) p.2)
  /-- The presented spectra jointly cover `T`. -/
  covers : ∀ x : T.left, ∃ p, ∃ hp : p ∈ pieces, ∃ y, presentedHom (isAffine p hp) p.2 y = x
  /-- The section of `F` on each presented covering piece. -/
  val : ∀ p (hp : p ∈ pieces), F.obj (op (presentedOver T (isAffine p hp) p.2))
  /-- The family is compatible on overlaps of covering pieces. -/
  compatible : ∀ {p q} (hp : p ∈ pieces) (hq : q ∈ pieces) {W : Over S}
    (a : W ⟶ presentedOver T (isAffine p hp) p.2)
    (b : W ⟶ presentedOver T (isAffine q hq) q.2),
    a ≫ presentedOverHom T (isAffine p hp) p.2 =
        b ≫ presentedOverHom T (isAffine q hq) q.2 →
      F.map a.op (val p hp) = F.map b.op (val q hq)

/-- The pieces of the pullback of an fppf matching family along `f : T' ⟶ T`. -/
def FppfMatching.restrictPieces {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T) :
    Set (Σ U : T'.left.Opens, PresentedAlgebra U) :=
  { q | ∃ p ∈ s.pieces, ∃ (_ : IsAffineOpen q.1) (hle : q.1 ≤ f.left ⁻¹ᵁ p.1),
      q.2 = p.2.map (f.left.appLE p.1 q.1 hle) }

/-- Membership in a restricted fppf matching family unpacks to a presented piece of the
original family together with an affine open of the source contained in the preimage. -/
theorem FppfMatching.mem_restrictPieces {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} :
    q ∈ s.restrictPieces f ↔
      ∃ p ∈ s.pieces, ∃ (_ : IsAffineOpen q.1) (hle : q.1 ≤ f.left ⁻¹ᵁ p.1),
        q.2 = p.2.map (f.left.appLE p.1 q.1 hle) :=
  Iff.rfl

/-- The affine-open witness extracted from membership in a restricted matching family. -/
def FppfMatching.restrictIsAffine {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    IsAffineOpen q.1 :=
  Exists.choose (Exists.choose_spec hq).2

/-- The original piece extracted from membership in a restricted matching family. -/
def FppfMatching.restrictPiece {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    Σ U : T.left.Opens, PresentedAlgebra U :=
  Exists.choose hq

/-- The original piece of a restricted matching family lies in the original family. -/
def FppfMatching.restrictPiece_mem {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    s.restrictPiece f hq ∈ s.pieces :=
  (Exists.choose_spec hq).1

/-- The inclusion of a restricted affine open in the preimage of the original open. -/
def FppfMatching.restrictLE {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    q.1 ≤ f.left ⁻¹ᵁ (s.restrictPiece f hq).1 :=
  Exists.choose (Exists.choose_spec (Exists.choose_spec hq).2)

/-- The restricted presentation is the coefficient-wise base change of the original
presentation. -/
def FppfMatching.restrictPiece_map {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    q.2 = (s.restrictPiece f hq).2.map
      (f.left.appLE (s.restrictPiece f hq).1 q.1 (s.restrictLE f hq)) :=
  Exists.choose_spec (Exists.choose_spec (Exists.choose_spec hq).2)

/-- The value of a restricted matching family on a pulled-back presented piece. -/
def FppfMatching.restrictVal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    (q : Σ U : T'.left.Opens, PresentedAlgebra U) (hq : q ∈ s.restrictPieces f) :
    F.obj (op (presentedOver T' (s.restrictIsAffine f hq) q.2)) :=
  F.map (eqToHom
      (congrArg (presentedOver T' (s.restrictIsAffine f hq)) (s.restrictPiece_map f hq))).op
    (F.map (presentedOverMap f (s.isAffine (s.restrictPiece f hq) (s.restrictPiece_mem f hq))
        (s.restrictPiece f hq).2 (s.restrictIsAffine f hq) (s.restrictLE f hq)).op
      (s.val (s.restrictPiece f hq) (s.restrictPiece_mem f hq)))

/-- Restricted presented covering morphisms are flat. -/
theorem FppfMatching.restrict_isFlat {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T) :
    ∀ q (hq : q ∈ s.restrictPieces f),
      AlgebraicGeometry.Flat (presentedHom (s.restrictIsAffine f hq) q.2) :=
  sorry

/-- Restricted presented covering morphisms are locally of finite presentation. -/
theorem FppfMatching.restrict_isLocallyOfFinitePresentation {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T) :
    ∀ q (hq : q ∈ s.restrictPieces f),
      AlgebraicGeometry.LocallyOfFinitePresentation
        (presentedHom (s.restrictIsAffine f hq) q.2) :=
  sorry

/-- Restricted presented covering pieces jointly cover the source. -/
theorem FppfMatching.restrict_covers {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T) :
    ∀ x : T'.left, ∃ q, ∃ hq : q ∈ s.restrictPieces f, ∃ y,
      presentedHom (s.restrictIsAffine f hq) q.2 y = x :=
  sorry

/-- Restricted sections agree on overlaps of the presented covering pieces. -/
theorem FppfMatching.restrict_compatible {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T) :
    ∀ {p q} (hp : p ∈ s.restrictPieces f) (hq : q ∈ s.restrictPieces f)
      {W : Over S}
      (a : W ⟶ presentedOver T' (s.restrictIsAffine f hp) p.2)
      (b : W ⟶ presentedOver T' (s.restrictIsAffine f hq) q.2),
      a ≫ presentedOverHom T' (s.restrictIsAffine f hp) p.2 =
          b ≫ presentedOverHom T' (s.restrictIsAffine f hq) q.2 →
        F.map a.op (s.restrictVal f p hp) = F.map b.op (s.restrictVal f q hq) :=
  sorry

/-- Restriction of an fppf matching family along a morphism of schemes over `S`. -/
def FppfMatching.restrict {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T T' : Over S}
    (f : T' ⟶ T) (s : FppfMatching F T) : FppfMatching F T' where
  pieces := s.restrictPieces f
  isAffine q hq := s.restrictIsAffine f hq
  isFlat := s.restrict_isFlat f
  isLocallyOfFinitePresentation := s.restrict_isLocallyOfFinitePresentation f
  covers := s.restrict_covers f
  val q hq := s.restrictVal f q hq
  compatible := s.restrict_compatible f

/-- Affine opens of `T` with the trivial presented algebra, as fppf covering pieces. -/
def FppfMatching.trivialPieces {S : Scheme.{u}} (T : Over S) :
    Set (Σ U : T.left.Opens, PresentedAlgebra U) :=
  (fun U : T.left.Opens ↦ (⟨U, PresentedAlgebra.trivial U⟩ : Σ U, PresentedAlgebra U)) ''
    {U | IsAffineOpen U}

/-- A piece in `trivialPieces T` is supported on an affine open. -/
def FppfMatching.trivialPieces_isAffine {S : Scheme.{u}} {T : Over S}
    {p : Σ U : T.left.Opens, PresentedAlgebra U} (hp : p ∈ FppfMatching.trivialPieces T) :
    IsAffineOpen p.1 :=
  (congrArg (fun q : Σ U : T.left.Opens, PresentedAlgebra U ↦ q.1)
      (Exists.choose_spec ((Set.mem_image _ {U | IsAffineOpen U} p).mp hp)).2) ▸
    (Exists.choose_spec ((Set.mem_image _ {U | IsAffineOpen U} p).mp hp)).1

/-- Trivial presented affine covering morphisms are flat. -/
theorem FppfMatching.ofSection_isFlat {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (x : F.obj (op T)) :
    ∀ p (hp : p ∈ FppfMatching.trivialPieces T),
      AlgebraicGeometry.Flat (presentedHom (FppfMatching.trivialPieces_isAffine hp) p.2) :=
  sorry

/-- Trivial presented affine covering morphisms are locally of finite presentation. -/
theorem FppfMatching.ofSection_isLocallyOfFinitePresentation {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (x : F.obj (op T)) :
    ∀ p (hp : p ∈ FppfMatching.trivialPieces T),
      AlgebraicGeometry.LocallyOfFinitePresentation
        (presentedHom (FppfMatching.trivialPieces_isAffine hp) p.2) :=
  sorry

/-- Trivial presented affine pieces jointly cover the scheme. -/
theorem FppfMatching.ofSection_covers {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (x : F.obj (op T)) :
    ∀ t : T.left, ∃ p, ∃ hp : p ∈ FppfMatching.trivialPieces T, ∃ y,
      presentedHom (FppfMatching.trivialPieces_isAffine hp) p.2 y = t :=
  sorry

/-- Restrictions of a global section agree on overlaps of trivial presented affine pieces. -/
theorem FppfMatching.ofSection_compatible {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (x : F.obj (op T)) :
    ∀ {p q} (hp : p ∈ FppfMatching.trivialPieces T)
      (hq : q ∈ FppfMatching.trivialPieces T) {W : Over S}
      (a : W ⟶ presentedOver T (FppfMatching.trivialPieces_isAffine hp) p.2)
      (b : W ⟶ presentedOver T (FppfMatching.trivialPieces_isAffine hq) q.2),
      a ≫ presentedOverHom T (FppfMatching.trivialPieces_isAffine hp) p.2 =
          b ≫ presentedOverHom T (FppfMatching.trivialPieces_isAffine hq) q.2 →
        F.map a.op (F.map
          (presentedOverHom T (FppfMatching.trivialPieces_isAffine hp) p.2).op x) =
        F.map b.op (F.map
          (presentedOverHom T (FppfMatching.trivialPieces_isAffine hq) q.2).op x) :=
  sorry

/-- The affine-open fppf matching family associated to a global section of `F`. -/
def FppfMatching.ofSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (x : F.obj (op T)) : FppfMatching F T where
  pieces := FppfMatching.trivialPieces T
  isAffine _ hp := FppfMatching.trivialPieces_isAffine hp
  isFlat := FppfMatching.ofSection_isFlat x
  isLocallyOfFinitePresentation := FppfMatching.ofSection_isLocallyOfFinitePresentation x
  covers := FppfMatching.ofSection_covers x
  val p hp := F.map (presentedOverHom T (FppfMatching.trivialPieces_isAffine hp) p.2).op x
  compatible := FppfMatching.ofSection_compatible x

/-- Two fppf matching families of `F` on `T` agree on a common fppf refinement when
there is a jointly covering family of presented algebras over affine opens of `T`,
indexed through a piece of each family, each of whose structure morphisms to `T` is
flat and locally of finite presentation, that pull the two families back to equal
sections of `F`. The refinement cannot be an arbitrary jointly surjective family of
schemes over `T`: a non-flat thickening such as `Spec k ⟶ Spec k[ε]` is excluded. -/
def FppfMatching.Agree {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (s t : FppfMatching F T) : Prop :=
  ∃ (ι : Type u) (U : ι → T.left.Opens) (A : ∀ i, PresentedAlgebra (U i))
    (hU : ∀ i, IsAffineOpen (U i))
    (p : ι → Σ V : T.left.Opens, PresentedAlgebra V)
    (q : ι → Σ V : T.left.Opens, PresentedAlgebra V)
    (hp : ∀ i, p i ∈ s.pieces) (hq : ∀ i, q i ∈ t.pieces)
    (fp : ∀ i,
      presentedOver T (hU i) (A i) ⟶
        presentedOver T (s.isAffine (p i) (hp i)) (p i).2)
    (fq : ∀ i,
      presentedOver T (hU i) (A i) ⟶
        presentedOver T (t.isAffine (q i) (hq i)) (q i).2),
    (∀ i, AlgebraicGeometry.Flat (presentedHom (hU i) (A i))) ∧
      (∀ i,
        AlgebraicGeometry.LocallyOfFinitePresentation
          (presentedHom (hU i) (A i))) ∧
      (∀ i,
        fp i ≫ presentedOverHom T (s.isAffine (p i) (hp i)) (p i).2 =
          presentedOverHom T (hU i) (A i)) ∧
      (∀ i,
        fq i ≫ presentedOverHom T (t.isAffine (q i) (hq i)) (q i).2 =
          presentedOverHom T (hU i) (A i)) ∧
      (∀ x : T.left, ∃ i y, presentedHom (hU i) (A i) y = x) ∧
        ∀ i, F.map (fp i).op (s.val (p i) (hp i)) =
          F.map (fq i).op (t.val (q i) (hq i))

/-- Restriction of matching families preserves agreement on a common fppf refinement. -/
theorem FppfMatching.agree_restrict {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) {s t : FppfMatching F T} (h : s.Agree t) :
    (s.restrict f).Agree (t.restrict f) :=
  sorry

/-- Applying a natural transformation to matching sections preserves compatibility. -/
theorem FppfMatching.mapNat_compatible {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G) {T : Over S} (s : FppfMatching F T) :
    ∀ {p q} (hp : p ∈ s.pieces) (hq : q ∈ s.pieces) {W : Over S}
      (a : W ⟶ presentedOver T (s.isAffine p hp) p.2)
      (b : W ⟶ presentedOver T (s.isAffine q hq) q.2),
      a ≫ presentedOverHom T (s.isAffine p hp) p.2 =
          b ≫ presentedOverHom T (s.isAffine q hq) q.2 →
        G.map a.op (η.app (op (presentedOver T (s.isAffine p hp) p.2)) (s.val p hp)) =
        G.map b.op (η.app (op (presentedOver T (s.isAffine q hq) q.2)) (s.val q hq)) :=
  sorry

/-- Push a matching family of `F` forward along a natural transformation `F ⟶ G`. -/
def FppfMatching.mapNat {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    {T : Over S} (s : FppfMatching F T) : FppfMatching G T where
  pieces := s.pieces
  isAffine := s.isAffine
  isFlat := s.isFlat
  isLocallyOfFinitePresentation := s.isLocallyOfFinitePresentation
  covers := s.covers
  val p hp := η.app (op (presentedOver T (s.isAffine p hp) p.2)) (s.val p hp)
  compatible := s.mapNat_compatible η

/-- Forward images of agreeing matching families still agree. -/
theorem FppfMatching.agree_mapNat {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) {T : Over S} {s t : FppfMatching F T} (h : s.Agree t) :
    (s.mapNat η).Agree (t.mapNat η) :=
  sorry

/-- The covering arrows of an fppf matching family. -/
def FppfMatching.arrow {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (s : FppfMatching F T) (p : s.pieces) :
    presentedOver T (s.isAffine p.1 p.2) p.1.2 ⟶ T :=
  presentedOverHom T (s.isAffine p.1 p.2) p.1.2

/-- Restriction by the identity acts trivially on quotient classes of matching families. -/
theorem plusTypeU_map_id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (T : (Over S)ᵒᵖ) :
    (TypeCat.ofHom <| Quot.map (fun s : FppfMatching F T.unop ↦ s.restrict (𝟙 T).unop)
      (fun _ _ h ↦ FppfMatching.agree_restrict (𝟙 T).unop h)) =
      𝟙 (Quot (fun s t : FppfMatching F T.unop ↦ s.Agree t)) :=
  sorry

/-- Successive restrictions agree with restriction by the composite on quotient classes. -/
theorem plusTypeU_map_comp {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    {T T' T'' : (Over S)ᵒᵖ} (f : T ⟶ T') (g : T' ⟶ T'') :
    (TypeCat.ofHom <| Quot.map
      (fun s : FppfMatching F T.unop ↦ s.restrict (f ≫ g).unop)
      (fun _ _ h ↦ FppfMatching.agree_restrict (f ≫ g).unop h)) =
    (TypeCat.ofHom <| Quot.map (fun s : FppfMatching F T.unop ↦ s.restrict f.unop)
      (fun _ _ h ↦ FppfMatching.agree_restrict f.unop h)) ≫
    (TypeCat.ofHom <| Quot.map (fun s : FppfMatching F T'.unop ↦ s.restrict g.unop)
      (fun _ _ h ↦ FppfMatching.agree_restrict g.unop h)) :=
  sorry

/-- The Type-`u` plus construction: matching families of presented fppf covers, quotiented
by agreement on a common fppf refinement. -/
def plusTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Quot (fun s t : FppfMatching F T.unop ↦ s.Agree t)
  map {T T'} f :=
    TypeCat.ofHom <|
      Quot.map (fun s : FppfMatching F T.unop ↦ s.restrict f.unop)
        fun _ _ h ↦ FppfMatching.agree_restrict f.unop h
  map_id := plusTypeU_map_id F
  map_comp := plusTypeU_map_comp F

/-- The value of the plus construction is the quotient of matching families by agreement
on a common fppf refinement. -/
theorem plusTypeU_obj {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (T : (Over S)ᵒᵖ) :
    (plusTypeU F).obj T = Quot (fun s t : FppfMatching F T.unop ↦ s.Agree t) :=
  rfl

/-- The classes of matching families associated to global sections commute with restriction. -/
theorem toPlusTypeU_naturality {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    F.map f ≫ (TypeCat.ofHom fun x ↦ Quot.mk _ (FppfMatching.ofSection x)) =
      (TypeCat.ofHom fun x ↦ Quot.mk _ (FppfMatching.ofSection x)) ≫ (plusTypeU F).map f :=
  sorry

/-- The unit of the plus construction, sending a global section to the class of its
affine-open matching family. -/
def toPlusTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : F ⟶ plusTypeU F where
  app T := TypeCat.ofHom fun x ↦ Quot.mk _ (FppfMatching.ofSection x)
  naturality {T T'} f := toPlusTypeU_naturality F f

/-- Pushing matching sections along a natural transformation commutes with restriction
on quotient classes. -/
theorem plusTypeUMap_naturality {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (plusTypeU F).map f ≫
      (TypeCat.ofHom <| Quot.map (fun s : FppfMatching F T'.unop ↦ s.mapNat η)
        (fun _ _ h ↦ FppfMatching.agree_mapNat η h)) =
    (TypeCat.ofHom <| Quot.map (fun s : FppfMatching F T.unop ↦ s.mapNat η)
      (fun _ _ h ↦ FppfMatching.agree_mapNat η h)) ≫ (plusTypeU G).map f :=
  sorry

/-- Functoriality of the plus construction on morphisms of Type-`u` presheaves. -/
def plusTypeUMap {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G) :
    plusTypeU F ⟶ plusTypeU G where
  app T :=
    TypeCat.ofHom <|
      Quot.map (fun s : FppfMatching F T.unop ↦ s.mapNat η)
        fun _ _ h ↦ FppfMatching.agree_mapNat η h
  naturality {T T'} f := plusTypeUMap_naturality η f

/-- The arrows of a presented fppf matching family generate a covering sieve. -/
theorem FppfMatching.arrow_covering {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T : Over S} (s : FppfMatching F T) :
    Sieve.ofArrows _ (fun p : s.pieces ↦ s.arrow p) ∈ (Scheme.fppfTopology.over S) T :=
  sorry

/-- Images of matching sections form a compatible family of maps from the singleton type. -/
theorem FppfMatching.amalgamate_compatible {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G) {T : Over S} (s : FppfMatching F T) :
    ∀ {W : Over S} {p q : s.pieces}
      (a : W ⟶ presentedOver T (s.isAffine p.1 p.2) p.1.2)
      (b : W ⟶ presentedOver T (s.isAffine q.1 q.2) q.1.2),
      a ≫ s.arrow p = b ≫ s.arrow q →
        (TypeCat.ofHom fun _ : PUnit.{u + 1} ↦
          η.app (op (presentedOver T (s.isAffine p.1 p.2) p.1.2)) (s.val p.1 p.2)) ≫
            G.map a.op =
        (TypeCat.ofHom fun _ : PUnit.{u + 1} ↦
          η.app (op (presentedOver T (s.isAffine q.1 q.2) q.1.2)) (s.val q.1 q.2)) ≫
            G.map b.op :=
  sorry

/-- The amalgamation of a matching family of sections of an fppf sheaf along its
presented covering arrows. -/
def FppfMatching.amalgamate {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) {T : Over S}
    (s : FppfMatching F T) : G.obj (op T) :=
  (hG.amalgamateOfArrows (fun p : s.pieces ↦ s.arrow p) s.arrow_covering
    (fun p ↦ TypeCat.ofHom fun _ : PUnit.{u + 1} ↦
      η.app (op (presentedOver T (s.isAffine p.1 p.2) p.1.2)) (s.val p.1 p.2))
    (fun {W} {p q} a b h ↦ s.amalgamate_compatible η a b h)) PUnit.unit

/-- Agreeing matching families amalgamate to the same section of a sheaf. -/
theorem FppfMatching.amalgamate_agree {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) {T : Over S}
    {s t : FppfMatching F T} (h : s.Agree t) :
    s.amalgamate η hG = t.amalgamate η hG :=
  sorry

/-- Amalgamation into a sheaf commutes with restriction on quotient classes. -/
theorem plusTypeULift_naturality {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (plusTypeU F).map f ≫
      (TypeCat.ofHom <| Quot.lift (fun s : FppfMatching F T'.unop ↦ s.amalgamate η hG)
        (fun _ _ h ↦ FppfMatching.amalgamate_agree η hG h)) =
    (TypeCat.ofHom <| Quot.lift (fun s : FppfMatching F T.unop ↦ s.amalgamate η hG)
      (fun _ _ h ↦ FppfMatching.amalgamate_agree η hG h)) ≫ G.map f :=
  sorry

/-- The lift of a morphism into an fppf sheaf through the plus construction. -/
def plusTypeULift {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    plusTypeU F ⟶ G where
  app T :=
    TypeCat.ofHom <|
      Quot.lift (fun s : FppfMatching F T.unop ↦ s.amalgamate η hG)
        fun _ _ h ↦ FppfMatching.amalgamate_agree η hG h
  naturality {T T'} f := plusTypeULift_naturality η hG f

/-- Type-`u` fppf sheafification of a Type-`u` presheaf on `Over S`, as the double plus
construction: matching families of presented fppf covers, quotiented by agreement on a
common fppf refinement, applied twice. -/
def sheafifyTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S)ᵒᵖ ⥤ Type u :=
  plusTypeU (plusTypeU F)

/-- The value of Type-`u` fppf sheafification is the double quotient of matching families
by agreement on a common fppf refinement. -/
theorem sheafifyTypeU_obj {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (T : (Over S)ᵒᵖ) :
    (sheafifyTypeU F).obj T = (plusTypeU (plusTypeU F)).obj T :=
  rfl

/-- The Type-`u` fppf sheafification of a Type-`u` presheaf is an fppf sheaf. -/
theorem sheafifyTypeU_isSheaf {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (sheafifyTypeU F) :=
  sorry

/-- The unit of Type-`u` fppf sheafification. -/
def toSheafifyTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    F ⟶ sheafifyTypeU F :=
  toPlusTypeU F ≫ plusTypeUMap (toPlusTypeU F)

/-- The unit of Type-`u` fppf sheafification factors as the double plus unit. -/
theorem toSheafifyTypeU_eq {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    toSheafifyTypeU F = toPlusTypeU F ≫ plusTypeUMap (toPlusTypeU F) :=
  rfl

/-- The lift of a morphism into an fppf sheaf through Type-`u` sheafification. -/
def sheafifyTypeULift {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    sheafifyTypeU F ⟶ G :=
  plusTypeULift (plusTypeULift η hG) hG

/-- `sheafifyTypeULift` is the double plus lift into an fppf sheaf. -/
theorem sheafifyTypeULift_eq {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    sheafifyTypeULift η hG = plusTypeULift (plusTypeULift η hG) hG :=
  rfl

/-- The sheafification lift factors the original map through the unit, and is the
unique morphism with this factorization. -/
theorem sheafifyTypeULift_spec {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    toSheafifyTypeU F ≫ sheafifyTypeULift η hG = η ∧
      ∀ g : sheafifyTypeU F ⟶ G,
        toSheafifyTypeU F ≫ g = η → g = sheafifyTypeULift η hG :=
  sorry

end AlgebraicGeometry.Scheme.FppfSheafification
