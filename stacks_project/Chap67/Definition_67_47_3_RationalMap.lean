/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap65.Definition_65_12_6_Site
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Rational maps of algebraic spaces

A partial map of algebraic spaces is a morphism defined on a dense open subspace.
A rational map is an equivalence class of partial maps, identified when they agree
on a further dense open.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Functor-of-points pullbacks exist in the presheaf category on schemes over `S`. -/
instance instHasPullbacksFunctorOfPoints : HasPullbacks ((Over S)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- A morphism of algebraic spaces, as a natural transformation of functors of points. -/
def rationalMapToFunctorOfPoints {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  f

/-- `rationalMapToFunctorOfPoints f` is the underlying natural transformation of `f`. -/
theorem rationalMapToFunctorOfPoints_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    rationalMapToFunctorOfPoints f = f :=
  sorry

/-- The fibre product of two morphisms of algebraic spaces, as an algebraic space, formed as
the pullback of their functors of points. -/
def domainInf {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) : AlgebraicSpace S :=
  ofFunctor (pullback (rationalMapToFunctorOfPoints ι) (rationalMapToFunctorOfPoints j)) sorry sorry sorry

/-- The functor of points of `domainInf ι j` is the functor-category pullback of `ι` and `j`. -/
theorem domainInf_functorOfPoints {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    (domainInf ι j).functorOfPoints =
      pullback (rationalMapToFunctorOfPoints ι) (rationalMapToFunctorOfPoints j) :=
  sorry

/-- The first projection of functors of points for `domainInf ι j`. -/
def domainInfFstNat {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    (domainInf ι j).functorOfPoints ⟶ U.functorOfPoints :=
  pullback.fst (rationalMapToFunctorOfPoints ι) (rationalMapToFunctorOfPoints j)

/-- The second projection of functors of points for `domainInf ι j`. -/
def domainInfSndNat {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    (domainInf ι j).functorOfPoints ⟶ V.functorOfPoints :=
  pullback.snd (rationalMapToFunctorOfPoints ι) (rationalMapToFunctorOfPoints j)

/-- The first projection `U ×_X V ⟶ U`. -/
def domainInfFst {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    domainInf ι j ⟶ U :=
  domainInfFstNat ι j

/-- The second projection `U ×_X V ⟶ V`. -/
def domainInfSnd {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    domainInf ι j ⟶ V :=
  domainInfSndNat ι j

/-- The structure morphism `U ×_X V ⟶ X`. -/
def domainInfHom {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    domainInf ι j ⟶ X :=
  domainInfFst ι j ≫ ι

/-- The two projections of `domainInf` agree after composing to `X`. -/
theorem domainInf_condition {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X) :
    domainInfFst ι j ≫ ι = domainInfSnd ι j ≫ j :=
  sorry

/-- The fibre product of two open immersions into `X` remains an open immersion into `X`. -/
instance instIsOpenImmersionDomainInfHom {U V X : AlgebraicSpace S} (ι : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion ι] [IsOpenImmersion j] : IsOpenImmersion (domainInfHom ι j) :=
  sorry

/-- An open immersion `ι : U ⟶ X` of algebraic spaces is dense when every nonempty open
subspace of `X` meets `U`. -/
def IsDense {U X : AlgebraicSpace S} (ι : U ⟶ X) : Prop :=
  ∀ (V : smallZariskiSite X),
    Nonempty (Points V.left) → Nonempty (Points (domainInf ι V.hom))

/-- The identity morphism of an algebraic space is a dense open immersion. -/
theorem isDense_id (X : AlgebraicSpace S) : IsDense (𝟙 X) :=
  sorry

/-- The fibre product of two dense open immersions is again dense in the target. -/
theorem isDense_domainInfHom {U V X : AlgebraicSpace S} {ι : U ⟶ X} {j : V ⟶ X}
    (hι : IsDense ι) (hj : IsDense j) : IsDense (domainInfHom ι j) :=
  sorry

/-- The whole space, as an object of the small Zariski site. -/
def idObj (X : AlgebraicSpace S) : smallZariskiSite X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance

/-- The structure morphism of `idObj X` is the identity on `X`. -/
theorem idObj_hom (X : AlgebraicSpace S) : (idObj X).hom = 𝟙 X :=
  sorry

/-- The fibre product of two open subspaces, as an object of the small Zariski site. -/
def domainInfSite {X : AlgebraicSpace S} (U V : smallZariskiSite X) : smallZariskiSite X :=
  MorphismProperty.Over.mk ⊤ (domainInfHom U.hom V.hom) sorry

/-- The structure morphism of `domainInfSite U V` is the fibre-product projection to `X`. -/
theorem domainInfSite_hom {X : AlgebraicSpace S} (U V : smallZariskiSite X) :
    (domainInfSite U V).hom = domainInfHom U.hom V.hom :=
  sorry

/-- A partial map from `X` to `Y` is a morphism into `Y` defined on a dense open subspace of
`X`. -/
structure PartialMap (X Y : AlgebraicSpace S) where
  /-- The domain of definition, as an open subspace of `X`. -/
  domain : smallZariskiSite X
  /-- The domain is dense in `X`. -/
  dense_domain : IsDense domain.hom
  /-- The underlying morphism on the domain. -/
  hom : domain.left ⟶ Y

namespace PartialMap

/-- A morphism of algebraic spaces, viewed as a partial map defined on the whole source. -/
def ofHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) : PartialMap X Y where
  domain := idObj X
  dense_domain := isDense_id X
  hom := f

/-- The underlying morphism of `ofHom f` is `f`. -/
theorem ofHom_hom {X Y : AlgebraicSpace S} (f : X ⟶ Y) : (ofHom f).hom = f :=
  sorry

/-- The domain of `ofHom f` is the whole source space. -/
theorem ofHom_domain_hom {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (ofHom f).domain.hom = 𝟙 X :=
  sorry

/-- Restrict a partial map along a morphism of dense open subspaces of the domain. -/
def restrict {X Y : AlgebraicSpace S} (f : PartialMap X Y) {U : smallZariskiSite X}
    (ιU : U ⟶ f.domain) (hU : IsDense U.hom) : PartialMap X Y where
  domain := U
  dense_domain := hU
  hom := ιU.left ≫ f.hom

/-- The underlying morphism of a restriction is the composite with the subspace inclusion. -/
theorem restrict_hom {X Y : AlgebraicSpace S} (f : PartialMap X Y) {U : smallZariskiSite X}
    (ιU : U ⟶ f.domain) (hU : IsDense U.hom) :
    (f.restrict ιU hU).hom = ιU.left ≫ f.hom :=
  sorry

/-- Two partial maps are equivalent if they agree after restriction to some dense open subspace
contained in both domains. -/
def equiv {X Y : AlgebraicSpace S} (f g : PartialMap X Y) : Prop :=
  ∃ (W : smallZariskiSite X) (hW : IsDense W.hom) (hWl : W ⟶ f.domain) (hWr : W ⟶ g.domain),
    (f.restrict hWl hW).hom = (g.restrict hWr hW).hom

/-- Equivalence of partial maps is reflexive. -/
theorem equiv_refl {X Y : AlgebraicSpace S} (f : PartialMap X Y) : equiv f f :=
  sorry

/-- The setoid of partial maps under agreement on a dense open. -/
def setoid (X Y : AlgebraicSpace S) : Setoid (PartialMap X Y) where
  r := equiv
  iseqv := sorry

/-- The setoid relation on partial maps is `PartialMap.equiv`. -/
theorem setoid_rel_iff {X Y : AlgebraicSpace S} (f g : PartialMap X Y) :
    setoid X Y f g ↔ equiv f g :=
  sorry

end PartialMap

/-- A rational map from `X` to `Y` is an equivalence class of partial maps. -/
def RationalMap (X Y : AlgebraicSpace S) : Type (u + 1) :=
  Quotient (PartialMap.setoid X Y)

/-- A partial map as a rational map. -/
def PartialMap.toRationalMap {X Y : AlgebraicSpace S} (f : PartialMap X Y) :
    RationalMap X Y :=
  Quotient.mk (PartialMap.setoid X Y) f

/-- Every rational map is represented by some partial map. -/
theorem RationalMap.exists_rep {X Y : AlgebraicSpace S} (f : RationalMap X Y) :
    ∃ g : PartialMap X Y, g.toRationalMap = f :=
  sorry

/-- Two partial maps determine the same rational map if and only if they are equivalent. -/
theorem PartialMap.toRationalMap_eq_iff {X Y : AlgebraicSpace S} {f g : PartialMap X Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g :=
  sorry

/-- Restriction along a smaller dense open does not change the associated rational map. -/
theorem PartialMap.restrict_toRationalMap {X Y : AlgebraicSpace S} (f : PartialMap X Y)
    {U : smallZariskiSite X} (ιU : U ⟶ f.domain) (hU : IsDense U.hom) :
    (f.restrict ιU hU).toRationalMap = f.toRationalMap :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
