/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Basic

/-!
# Domain of definition of rational maps of algebraic spaces

A rational map is defined at a point of `|X|` when some representative
partial map contains that point in its domain. The domain of definition
is the set of all such points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.ConcreteCategory MorphismProperty Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PartialMap

/-- The set of points of `|X|` lying in the domain of a partial map. -/
def points {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : PartialMap X Y) :
    Set (Points X) :=
  Set.range (Points.map f.domain.hom)

/-- Membership in the point-set of a partial map is being the image of a point
of the domain under the structure morphism. -/
theorem mem_points_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : PartialMap X Y} {x : Points X} :
    x ∈ f.points ↔ ∃ u : Points f.domain.left, Points.map f.domain.hom u = x :=
  Iff.rfl

end PartialMap

namespace RationalMap

/-- The domain of definition of a rational map: the set of points of `|X|` at
which some representative is defined. -/
def domain {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    Set (Points X) :=
  {x | ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ}

/-- A rational map is defined at a point if that point lies in its domain of
definition. -/
abbrev definedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) (x : Points X) : Prop :=
  x ∈ φ.domain

/-- A point lies in the domain of a rational map if and only if some
representative contains that point in its domain. -/
theorem mem_domain {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {φ : RationalMap X Y} {x : Points X} :
    x ∈ φ.domain ↔ ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ :=
  Iff.rfl

/-- A rational map is defined at a point if and only if some representative
contains that point in its domain. -/
theorem definedAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {φ : RationalMap X Y} {x : Points X} :
    φ.definedAt x ↔ ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ :=
  Iff.rfl

end RationalMap

namespace PartialMap

/-- The points of a partial map lie in the domain of definition of the associated
rational map. -/
theorem points_subset_domain {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) : g.points ⊆ g.toRationalMap.domain := by
  intro x hx
  exact ⟨g, hx, rfl⟩

end PartialMap

namespace RationalMap

/-- The subfunctor of maps into `X` whose image of points lands in the domain of
definition of `φ`. -/
def domainSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    Subfunctor X.functorOfPoints where
  obj T := {α | Set.range (Points.map (X := ofOver T.unop) (Y := X) (yonedaEquiv.symm α)) ⊆ φ.domain}
  map := sorry

/-- A section of `X` lies in `domainSubfunctor φ` if and only if its image of
points is contained in the domain of definition of `φ`. -/
theorem mem_domainSubfunctor_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) {T : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj T) :
    α ∈ (domainSubfunctor φ).obj T ↔
      Set.range (Points.map (X := ofOver T.unop) (Y := X) (yonedaEquiv.symm α)) ⊆ φ.domain :=
  Iff.rfl

/-- The domain subfunctor of a rational map is an fppf sheaf. -/
theorem domainSubfunctor_isSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (domainSubfunctor φ).toFunctor :=
  sorry

/-- The diagonal of the domain subfunctor of a rational map is representable. -/
theorem domainSubfunctor_representableDiagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) :
    yoneda.relativelyRepresentable (Limits.diag (domainSubfunctor φ).toFunctor) :=
  sorry

/-- The domain subfunctor admits a representable étale locally-surjective atlas. -/
theorem domainSubfunctor_hasEtaleAtlas {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ (domainSubfunctor φ).toFunctor),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  sorry

/-- The algebraic space underlying the domain of definition of `φ`. -/
def domainSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    AlgebraicSpace S :=
  ofFunctor (domainSubfunctor φ).toFunctor (domainSubfunctor_isSheaf φ)
    (domainSubfunctor_representableDiagonal φ) (domainSubfunctor_hasEtaleAtlas φ)

/-- The functor of points of `domainSpace φ` is the domain subfunctor of `φ`. -/
theorem domainSpace_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) :
    (domainSpace φ).functorOfPoints = (domainSubfunctor φ).toFunctor :=
  rfl

/-- The inclusion of the domain of definition of `φ` into `X`. -/
def domainι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainSpace ⟶ X :=
  (domainSubfunctor φ).ι

/-- The inclusion of the domain of definition is the subfunctor inclusion. -/
theorem domainι_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainι = (domainSubfunctor φ).ι :=
  rfl

/-- The inclusion of the domain of definition is an open immersion. -/
instance instIsOpenImmersion_domainι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) : IsOpenImmersion φ.domainι :=
  sorry

/-- The domain of definition of `φ`, as an object of the small Zariski site of `X`. -/
def domainSite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    smallZariskiSite X :=
  MorphismProperty.Over.mk ⊤ φ.domainι inferInstance

/-- The structure morphism of `domainSite φ` is the domain inclusion. -/
theorem domainSite_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainSite.hom = φ.domainι :=
  rfl

/-- The underlying space of `domainSite φ` is `domainSpace φ`. -/
theorem domainSite_left {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainSite.left = φ.domainSpace :=
  rfl

/-- A point of `X` lies in the domain of definition if and only if it lies in the
image of the domain inclusion. -/
theorem mem_domainSite_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) (x : Points X) :
    x ∈ Set.range (Points.map φ.domainι) ↔ x ∈ φ.domain :=
  sorry

/-- The domain of definition of a rational map is dense in `X`. -/
theorem dense_domainSite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    IsDense φ.domainι :=
  sorry

end RationalMap

namespace PartialMap

/-- A `T`-point of the domain of a partial map lands in the domain subfunctor of
the associated rational map. -/
theorem hom_app_mem_domainSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) {T : (Over S)ᵒᵖ} (α : g.domain.left.functorOfPoints.obj T) :
    g.domain.hom.app T α ∈ (g.toRationalMap.domainSubfunctor).obj T :=
  sorry

/-- The canonical factorization of a representative domain through the domain of
definition of the associated rational map. -/
def factorDomain {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : PartialMap X Y) :
    g.domain.left ⟶ g.toRationalMap.domainSpace where
  app T := ↾fun α ↦ ⟨g.domain.hom.app T α, hom_app_mem_domainSubfunctor g α⟩
  naturality := sorry

/-- The factorization of a representative domain through the domain of definition
recovers the structure morphism of that domain. -/
theorem factorDomain_comp_domainι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) :
    g.factorDomain ≫ g.toRationalMap.domainι = g.domain.hom := by
  apply NatTrans.ext
  rfl

/-- The factorization of a representative domain composes with the structure
morphism of the domain site to the structure morphism of that domain. -/
theorem factorDomain_comp_domainSite_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) :
    g.factorDomain ≫ g.toRationalMap.domainSite.hom = g.domain.hom :=
  factorDomain_comp_domainι g

/-- The factorization of a representative domain, as a morphism in the small
Zariski site of `X`. -/
def factorDomainSite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : PartialMap X Y) :
    g.domain ⟶ g.toRationalMap.domainSite :=
  MorphismProperty.Over.homMk g.factorDomain (factorDomain_comp_domainSite_hom g)

/-- The underlying morphism of `factorDomainSite g` is `factorDomain g`. -/
theorem factorDomainSite_left {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) :
    (factorDomainSite g).left = g.factorDomain :=
  rfl

end PartialMap

end AlgebraicGeometry.AlgebraicSpace
