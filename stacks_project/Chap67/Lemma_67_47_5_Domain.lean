/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap67.Definition_67_47_4_Domain

/-!
# Domain of definition of a rational map, as an open subspace

The domain of definition of a rational map of algebraic spaces is realized as
the open subspace of maps whose image of points lands in the point-set domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.ConcreteCategory MorphismProperty Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace RationalMap

/-- The subfunctor of maps into `X` whose image of points lands in the domain of
definition of `φ`. -/
def domainSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    Subfunctor X.functorOfPoints where
  obj T := {α | Set.range (Points.map (ofYonedaSection α)) ⊆ φ.domain}
  map := sorry

/-- A section of `X` lies in `domainSubfunctor φ` if and only if its image of
points is contained in the domain of definition of `φ`. -/
theorem mem_domainSubfunctor_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) {T : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj T) :
    α ∈ (domainSubfunctor φ).obj T ↔
      Set.range (Points.map (ofYonedaSection α)) ⊆ φ.domain :=
  sorry

/-- The algebraic space underlying the domain of definition of `φ`. -/
def domainSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    AlgebraicSpace S :=
  ofFunctor (domainSubfunctor φ).toFunctor sorry sorry sorry

/-- The functor of points of `domainSpace φ` is the domain subfunctor of `φ`. -/
theorem domainSpace_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) :
    (domainSpace φ).functorOfPoints = (domainSubfunctor φ).toFunctor :=
  sorry

/-- The inclusion of the domain of definition of `φ` into `X`. -/
def domainι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainSpace ⟶ X :=
  (domainSubfunctor φ).ι

/-- The inclusion of the domain of definition is the subfunctor inclusion. -/
theorem domainι_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainι = (domainSubfunctor φ).ι :=
  sorry

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
  sorry

/-- The underlying space of `domainSite φ` is `domainSpace φ`. -/
theorem domainSite_left {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    φ.domainSite.left = φ.domainSpace :=
  sorry

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
    g.factorDomain ≫ g.toRationalMap.domainι = g.domain.hom :=
  sorry

/-- The factorization of a representative domain composes with the structure
morphism of the domain site to the structure morphism of that domain. -/
theorem factorDomain_comp_domainSite_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) :
    g.factorDomain ≫ g.toRationalMap.domainSite.hom = g.domain.hom :=
  sorry

/-- The factorization of a representative domain, as a morphism in the small
Zariski site of `X`. -/
def factorDomainSite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : PartialMap X Y) :
    g.domain ⟶ g.toRationalMap.domainSite :=
  MorphismProperty.Over.homMk g.factorDomain (factorDomain_comp_domainSite_hom g)

/-- The underlying morphism of `factorDomainSite g` is `factorDomain g`. -/
theorem factorDomainSite_left {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) :
    (factorDomainSite g).left = g.factorDomain :=
  sorry

end PartialMap

end AlgebraicGeometry.AlgebraicSpace
