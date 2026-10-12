/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Lemma_67_47_5_Domain
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Canonical partial map on the domain of definition

If `X` is reduced and `Y` is separated, a rational map `φ : X ⤏ Y` is
represented by a unique morphism on its domain of definition, obtained by
gluing representative homs along the cover of that domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ConcreteCategory
  CategoryTheory.Functor.relativelyRepresentable Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace RationalMap

/-- A partial map representing the rational map `φ`. -/
abbrev Representative {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :=
  { g : PartialMap X Y // g.toRationalMap = φ }

/-- A term of `Representative φ` is a partial map representing `φ`. -/
theorem Representative_toRationalMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {φ : RationalMap X Y} (g : Representative φ) :
    g.val.toRationalMap = φ :=
  sorry

/-- The factorization of a representative domain into the domain of definition of
`φ`, after transporting along the representation equality. -/
def factorDomain_of {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    g.domain.left ⟶ φ.domainSpace :=
  g.factorDomain ≫ eqToHom (congrArg (fun ψ : RationalMap X Y ↦ ψ.domainSpace) hg)

/-- `factorDomain_of` is the transported factorization through the domain of
definition. -/
theorem factorDomain_of_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    factorDomain_of φ g hg =
      g.factorDomain ≫ eqToHom (congrArg (fun ψ : RationalMap X Y ↦ ψ.domainSpace) hg) :=
  sorry

/-- The transported factorization of a representative domain is an open immersion. -/
instance instIsOpenImmersion_factorDomain_of {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    IsOpenImmersion (factorDomain_of φ g hg) :=
  sorry

/-- The Yoneda morphism associated to a `T`-point of the domain of definition. -/
def domainSection {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T) :
    yoneda.obj T.unop ⟶ φ.domainSpace.functorOfPoints :=
  yonedaEquiv.symm α

/-- `domainSection` is the Yoneda inverse of a `T`-point of the domain of definition. -/
theorem domainSection_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T) :
    domainSection φ α = yonedaEquiv.symm α :=
  sorry

/-- The represented pullback of a representative domain along a `T`-point of the
domain of definition. -/
def gluedHomCoverObj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) : Over S :=
  (MorphismProperty.relative.rep (inferInstance : IsOpenImmersion (factorDomain_of φ g hg)).presheaf).pullback
    (domainSection φ α)

/-- The covering arrow over `T` from the represented pullback of a representative
domain. -/
def gluedHomCoverMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    gluedHomCoverObj φ α g hg ⟶ T.unop :=
  (MorphismProperty.relative.rep (inferInstance : IsOpenImmersion (factorDomain_of φ g hg)).presheaf).snd
    (domainSection φ α)

/-- The `T`-point of a representative domain obtained from the represented
pullback along a `T`-point of the domain of definition. -/
def gluedHomCoverLift {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    g.domain.left.functorOfPoints.obj (op (gluedHomCoverObj φ α g hg)) :=
  yonedaEquiv
    ((MorphismProperty.relative.rep (inferInstance : IsOpenImmersion (factorDomain_of φ g hg)).presheaf).fst
      (domainSection φ α))

/-- The local section of `Y` on a representative-domain pullback, obtained by
applying the representative hom. -/
def gluedHomCoverSection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    PUnit.{u + 1} ⟶ Y.functorOfPoints.obj (op (gluedHomCoverObj φ α g hg)) :=
  ↾fun _ ↦ g.hom.app (op (gluedHomCoverObj φ α g hg)) (gluedHomCoverLift φ α g hg)

/-- The represented pullbacks of representative domains form an fppf cover of `T`. -/
theorem gluedHomCover_mem {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T) :
    Sieve.ofArrows (fun g : Representative φ ↦ gluedHomCoverObj φ α g.val g.property)
      (fun g ↦ gluedHomCoverMap φ α g.val g.property) ∈ Scheme.fppfTopology.over S T.unop :=
  sorry

/-- Representative homs are compatible on overlaps of the represented pullbacks. -/
theorem gluedHomCoverSection_compatible {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    {W : Over S} {g₁ g₂ : Representative φ}
    (a : W ⟶ gluedHomCoverObj φ α g₁.val g₁.property)
    (b : W ⟶ gluedHomCoverObj φ α g₂.val g₂.property)
    (h : a ≫ gluedHomCoverMap φ α g₁.val g₁.property = b ≫ gluedHomCoverMap φ α g₂.val g₂.property) :
    gluedHomCoverSection φ α g₁.val g₁.property ≫ Y.functorOfPoints.map a.op =
      gluedHomCoverSection φ α g₂.val g₂.property ≫ Y.functorOfPoints.map b.op :=
  sorry

/-- The covering object is the represented pullback of `factorDomain_of` along the
Yoneda morphism of the given `T`-point. -/
theorem gluedHomCoverObj_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    gluedHomCoverObj φ α g hg =
      (MorphismProperty.relative.rep
          (inferInstance : IsOpenImmersion (factorDomain_of φ g hg)).presheaf).pullback
        (domainSection φ α) :=
  sorry

/-- The covering arrow is the second projection of the represented pullback. -/
theorem gluedHomCoverMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    gluedHomCoverMap φ α g hg =
      (MorphismProperty.relative.rep
          (inferInstance : IsOpenImmersion (factorDomain_of φ g hg)).presheaf).snd
        (domainSection φ α) :=
  sorry

/-- The lifted `T`-point of a representative domain is the Yoneda image of the
first projection of the represented pullback. -/
theorem gluedHomCoverLift_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    gluedHomCoverLift φ α g hg =
      yonedaEquiv
        ((MorphismProperty.relative.rep
            (inferInstance : IsOpenImmersion (factorDomain_of φ g hg)).presheaf).fst
          (domainSection φ α)) :=
  sorry

/-- Evaluating the local section at the unique point of `PUnit` applies the
representative hom to the lifted `T`-point. -/
theorem gluedHomCoverSection_apply {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    {T : (Over S)ᵒᵖ} (α : φ.domainSpace.functorOfPoints.obj T)
    (g : PartialMap X Y) (hg : g.toRationalMap = φ) :
    gluedHomCoverSection φ α g hg PUnit.unit =
      g.hom.app (op (gluedHomCoverObj φ α g hg)) (gluedHomCoverLift φ α g hg) :=
  sorry

/-- The unique morphism on the domain of definition obtained by amalgamating
representative homs along `factorDomain`, using that `Y.functorOfPoints` is an
fppf sheaf. -/
def gluedHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) :
    φ.domainSpace ⟶ Y where
  app T := ↾fun α ↦
    Y.isSheaf.amalgamateOfArrows
      (fun g : Representative φ ↦ gluedHomCoverMap φ α g.val g.property)
      (gluedHomCover_mem φ α)
      (fun g ↦ gluedHomCoverSection φ α g.val g.property)
      (fun {W} {g₁ g₂} a b h ↦ gluedHomCoverSection_compatible φ α a b h)
      PUnit.unit
  naturality := sorry

/-- Restricting `gluedHom φ` along the transported factorization of a representative
domain recovers that representative hom; this is the amalgamation identity. -/
theorem factorDomain_comp_gluedHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) {g : PartialMap X Y}
    (hg : g.toRationalMap = φ) :
    g.factorDomain ≫ eqToHom (congrArg (fun ψ : RationalMap X Y ↦ ψ.domainSpace) hg) ≫
        gluedHom φ =
      g.hom :=
  sorry

/-- The canonical partial-map representative of a rational map from a reduced
algebraic space to a separated algebraic space, defined on the whole domain of
definition. -/
def toPartialMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) :
    PartialMap X Y where
  domain := φ.domainSite
  dense_domain := dense_domainSite φ
  hom := gluedHom φ

/-- The domain of `toPartialMap φ` is the domain of definition of `φ`. -/
theorem toPartialMap_domain {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) :
    (toPartialMap φ).domain = φ.domainSite :=
  sorry

/-- The structure morphism of the domain of `toPartialMap φ` is the domain
inclusion. -/
theorem toPartialMap_domain_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) :
    (toPartialMap φ).domain.hom = φ.domainι :=
  sorry

/-- The underlying morphism of `toPartialMap φ` is the glued morphism on the
domain of definition. -/
theorem toPartialMap_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) :
    (toPartialMap φ).hom = gluedHom φ :=
  sorry

end RationalMap

namespace PartialMap

/-- Restricting the canonical representative of a partial map's rational map
along the factorization of its domain recovers the original morphism. -/
theorem toPartialMap_restrict_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (g : PartialMap X Y) :
    (g.toRationalMap.toPartialMap.restrict (factorDomainSite g) g.dense_domain).hom = g.hom :=
  sorry

end PartialMap

end AlgebraicGeometry.AlgebraicSpace
