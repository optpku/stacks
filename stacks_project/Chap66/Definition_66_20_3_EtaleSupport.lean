/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Definition_66_19_6_Stalk

/-!
# Support of an abelian sheaf on the small étale site of an algebraic space

The support of an abelian sheaf on `X_étale` is the set of points of `|X|` at which a
geometric stalk is a nonzero abelian group. The support of a local section is the closed
complement of the largest Zariski open of the underlying scheme on which the section
restricts to zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The scheme over `S` obtained by viewing a Zariski open of an object of `X_étale` as an
open subscheme. -/
def openImmersionOver (U : smallEtaleSite X) (W : U.left.left.Opens) : Over S :=
  Over.mk (W.ι ≫ U.left.hom)

/-- The structure morphism of `openImmersionOver U W` is the open immersion followed by the
structure morphism of `U`. -/
theorem openImmersionOver_hom (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionOver U W).hom = W.ι ≫ U.left.hom := sorry

/-- The open immersion of a Zariski open of `U`, as a morphism of schemes over `S`. -/
def openImmersionMap (U : smallEtaleSite X) (W : U.left.left.Opens) :
    openImmersionOver U W ⟶ U.left :=
  Over.homMk W.ι

/-- The underlying scheme morphism of `openImmersionMap U W` is the open immersion `W.ι`. -/
theorem openImmersionMap_left (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionMap U W).left = W.ι := sorry

/-- The open immersion of a Zariski open of `U`, as a morphism of algebraic spaces over `S`. -/
def openImmersionι (U : smallEtaleSite X) (W : U.left.left.Opens) :
    ofOver (openImmersionOver U W) ⟶ ofOver U.left :=
  ofOverMap (openImmersionMap U W)

/-- `openImmersionι U W` is `ofOverMap` of the over-morphism induced by the open immersion. -/
theorem openImmersionι_eq (U : smallEtaleSite X) (W : U.left.left.Opens) :
    openImmersionι U W = ofOverMap (openImmersionMap U W) := sorry

/-- The structure morphism of a Zariski open of `U`, as an étale morphism of algebraic spaces
into `X`. -/
instance etale_openImmersion_comp (U : smallEtaleSite X) (W : U.left.left.Opens) :
    Etale (openImmersionι U W ≫ U.hom) := sorry

/-- The object of `X_étale` associated to a Zariski open of the underlying scheme of `U`. -/
def openImmersionSite (U : smallEtaleSite X) (W : U.left.left.Opens) : smallEtaleSite X :=
  MorphismProperty.CostructuredArrow.mk ⊤ (openImmersionι U W ≫ U.hom)
    (etale_openImmersion_comp U W)

/-- The underlying scheme over `S` of `openImmersionSite U W` is `openImmersionOver U W`. -/
theorem openImmersionSite_left (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionSite U W).left = openImmersionOver U W := sorry

/-- The structure morphism of `openImmersionSite U W` is the composite of the open immersion
with `U.hom`. -/
theorem openImmersionSite_hom (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionSite U W).hom = openImmersionι U W ≫ U.hom := sorry

/-- The restriction arrow `W ⟶ U` in `X_étale` associated to a Zariski open of `U`. -/
def openImmersionHom (U : smallEtaleSite X) (W : U.left.left.Opens) :
    openImmersionSite U W ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk (openImmersionMap U W) trivial sorry

/-- The underlying morphism of schemes over `S` of `openImmersionHom U W` is
`openImmersionMap U W`. -/
theorem openImmersionHom_left (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionHom U W).left = openImmersionMap U W := sorry

/-- The underlying type-valued presheaf of an abelian sheaf on `X_étale`. -/
def abelianTypePresheaf (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1) :=
  F.obj ⋙ forget AddCommGrpCat.{u + 1}

/-- The type-valued presheaf of an abelian sheaf is the forgetful image of its underlying
presheaf. -/
theorem abelianTypePresheaf_eq (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    abelianTypePresheaf F = F.obj ⋙ forget AddCommGrpCat.{u + 1} := sorry

/-- Restriction of a local section of an abelian sheaf along a Zariski open of its domain
vanishes. -/
def vanishesOn (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) (W : U.left.left.Opens) : Prop :=
  F.obj.map ((openImmersionHom U W).op) σ = 0

/-- Vanishing on a Zariski open is vanishing of the restriction along `openImmersionHom`. -/
theorem vanishesOn_def (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) (W : U.left.left.Opens) :
    vanishesOn F U σ W ↔ F.obj.map ((openImmersionHom U W).op) σ = 0 := sorry

/-- The canonical largest Zariski open of `U` on which an étale section vanishes, as the
supremum of all vanishing opens. -/
def largestVanishingOpen (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) : U.left.left.Opens :=
  sSup (setOf (vanishesOn F U σ))

/-- The section vanishes on the canonical largest vanishing open. -/
theorem largestVanishingOpen_spec (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) :
    vanishesOn F U σ (largestVanishingOpen F U σ) := sorry

/-- Every Zariski open on which the section vanishes is contained in the canonical largest
vanishing open. -/
theorem le_largestVanishingOpen (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) (V : U.left.left.Opens) :
    vanishesOn F U σ V → V ≤ largestVanishingOpen F U σ := sorry

/-- The support of an abelian sheaf on the small étale site, as the points of `|X|` admitting a
geometric point with nonzero geometric stalk. -/
def abelianSheafSupport (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    Set (Points X) :=
  {x | ∃ xbar : GeometricPoint X,
    xbar.image = x ∧ ¬ Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F))}

/-- Membership in the étale abelian-sheaf support is existence of a geometric point over the
point with nonzero geometric stalk. -/
theorem mem_abelianSheafSupport_iff (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (x : Points X) :
    x ∈ abelianSheafSupport F ↔
      ∃ xbar : GeometricPoint X,
        xbar.image = x ∧ ¬ Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) :=
  sorry

/-- Geometric stalks of an abelian sheaf have the same subsingleton property for geometric
points with the same image in `|X|`. -/
theorem abelianSheafSupport_subsingleton_iff_of_image_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (xbar tbar : GeometricPoint X) (himage : xbar.image = tbar.image) :
    Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) ↔
      Subsingleton (GeometricPoint.stalk tbar (abelianTypePresheaf F)) := sorry

/-- For any geometric point, support membership of its image is equivalent to nonvanishing of
its geometric stalk; this is independent of the chosen geometric point over the same point of
`|X|`. -/
theorem mem_abelianSheafSupport_iff_stalk
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (xbar : GeometricPoint X) :
    xbar.image ∈ abelianSheafSupport F ↔
      ¬ Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) := sorry

/-- The support of an étale section, as the bundled closed complement of its largest vanishing
open. -/
def abelianSheafSectionSupport (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) : Closeds U.left.left :=
  Opens.compl (largestVanishingOpen F U σ)

/-- The closed support of a section is the complement of its canonical largest vanishing open. -/
theorem abelianSheafSectionSupport_def
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) :
    abelianSheafSectionSupport F U σ = Opens.compl (largestVanishingOpen F U σ) := sorry

/-- A point of the underlying scheme of `U` lies in the section support exactly when it does
not lie in the largest vanishing open. -/
theorem mem_abelianSheafSectionSupport_iff
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) (u : U.left.left) :
    u ∈ abelianSheafSectionSupport F U σ ↔ u ∉ largestVanishingOpen F U σ := sorry

end AlgebraicGeometry.AlgebraicSpace

end
