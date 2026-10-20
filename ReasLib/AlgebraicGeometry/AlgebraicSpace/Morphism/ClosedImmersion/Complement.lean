module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion

/-! # Open complements of closed immersions of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The image of `|Y|` in `|X|` along a morphism of algebraic spaces. -/
def pointsImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) : Set (Points X) :=
  Set.range (Points.map f)

/-- The image of points along `f` is the range of `Points.map f`. -/
theorem pointsImage_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    pointsImage f = Set.range (Points.map f) :=
  rfl

/-- The morphism of algebraic spaces associated to a Yoneda section of `X`. -/
def homOfYonedaSection {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : ofOver U.unop ⟶ X :=
  yonedaEquiv.symm α

/-- `homOfYonedaSection` is the Yoneda transpose of a section of the functor of points. -/
theorem homOfYonedaSection_eq {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) :
    homOfYonedaSection α = yonedaEquiv.symm α :=
  rfl

/-- A section of the functor of points of `X` misses the closed image of `i` when the
induced map on points lands in the complement of `|Z|`. -/
def missesClosedImage {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) : Prop :=
  pointsImage (homOfYonedaSection α) ⊆ (pointsImage i)ᶜ

/-- Missing the closed image of `i` is the point-set condition on the Yoneda morphism
associated to a section. -/
theorem missesClosedImage_iff {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    missesClosedImage i α ↔ pointsImage (homOfYonedaSection α) ⊆ (pointsImage i)ᶜ :=
  Iff.rfl

/-- The subfunctor of maps into `X` whose image of points misses `|Z|`. -/
def closedImmersionComplementSubfunctor {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : Subfunctor X.functorOfPoints :=
  OpenSubspace.Construction.subfunctor X ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
    (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩

/-- Membership in the complement subfunctor is the missing-closed-image condition. -/
theorem mem_closedImmersionComplementSubfunctor_obj {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    α ∈ (closedImmersionComplementSubfunctor i).obj U ↔ missesClosedImage i α :=
  Iff.rfl

/-- The open complement algebraic space `X \ Z` of a closed immersion `i : Z ⟶ X`. -/
def closedImmersionComplement {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    AlgebraicSpace S :=
  OpenSubspace.Construction.space X ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
    (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩

/-- The functor of points of the complement is the missing-`|Z|` subfunctor. -/
theorem closedImmersionComplement_functorOfPoints {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionComplement i).functorOfPoints =
      (closedImmersionComplementSubfunctor i).toFunctor :=
  rfl

/-- The open immersion of the complement `X \ Z` into `X`. -/
def closedImmersionComplementι {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement i ⟶ X :=
  OpenSubspace.Construction.ι X ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
    (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩

/-- The complement inclusion is the subfunctor inclusion of maps missing `|Z|`. -/
theorem closedImmersionComplementι_eq {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    closedImmersionComplementι i = (closedImmersionComplementSubfunctor i).ι :=
  rfl

/-- The image of `|X \ Z|` in `|X|` is the complement of `|Z|`. -/
theorem closedImmersionComplement_range {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    pointsImage (closedImmersionComplementι i) = (pointsImage i)ᶜ :=
  OpenSubspace.Construction.inclusion_range X ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
    (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩

/-- The complement space is the missing-`|Z|` subfunctor, included by an open immersion
whose image of points is the complement of `|Z|`. -/
theorem closedImmersionComplement_spec {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (closedImmersionComplement i).functorOfPoints =
        (closedImmersionComplementSubfunctor i).toFunctor ∧
      closedImmersionComplementι i = (closedImmersionComplementSubfunctor i).ι ∧
      IsOpenImmersion (closedImmersionComplementι i) ∧
      pointsImage (closedImmersionComplementι i) = (pointsImage i)ᶜ :=
  ⟨closedImmersionComplement_functorOfPoints i, closedImmersionComplementι_eq i,
    OpenSubspace.Construction.inclusion_isOpenImmersion X
      ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
        (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩,
    closedImmersionComplement_range i⟩

/-- The inclusion of the complement of a closed immersion is an open immersion. -/
instance instIsOpenImmersion_closedImmersionComplementι {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : IsOpenImmersion (closedImmersionComplementι i) :=
  (closedImmersionComplement_spec i).2.2.1

/-- The complement of a closed immersion, as an open subspace of `X`. -/
def closedImmersionComplementSubspace {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : OpenSubspace X :=
  OpenSubspace.ofι (closedImmersionComplementι i)

/-- The composite of the complement inclusion of `inverseImageι f i` with `f` misses the
closed image of `i`. -/
private theorem restrictToComplement_misses {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    ∀ (W : (Over S)ᵒᵖ)
      (t : (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W),
      missesClosedImage i ((closedImmersionComplementι (inverseImageι f i) ≫ f).app W t) :=
  sorry

/-- The section maps between complements commute with morphisms of test objects. -/
private theorem restrictToComplement_naturality {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {W W' : (Over S)ᵒᵖ} (g : W ⟶ W') :
    (closedImmersionComplement (inverseImageι f i)).functorOfPoints.map g ≫
        (TypeCat.ofHom fun t :
            (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W' ↦
          (⟨(closedImmersionComplementι (inverseImageι f i) ≫ f).app W' t,
            restrictToComplement_misses f i W' t⟩ :
              (closedImmersionComplement i).functorOfPoints.obj W')) =
      (TypeCat.ofHom fun t :
          (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W ↦
        (⟨(closedImmersionComplementι (inverseImageι f i) ≫ f).app W t,
          restrictToComplement_misses f i W t⟩ :
            (closedImmersionComplement i).functorOfPoints.obj W)) ≫
        (closedImmersionComplement i).functorOfPoints.map g :=
  sorry

/-- The restriction of `f : Y ⟶ X` to the open complements of `i` and of
`inverseImageι f i`. -/
@[no_expose] def restrictToComplement {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι f i) ⟶ closedImmersionComplement i where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (inverseImageι f i) ≫ f).app W t,
      restrictToComplement_misses f i W t⟩
  naturality _ _ g := restrictToComplement_naturality f i g

/-- The underlying map of `restrictToComplement f i` on sections is the composite
`closedImmersionComplementι (inverseImageι f i) ≫ f`. -/
theorem restrictToComplement_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] {W : (Over S)ᵒᵖ}
    (t : (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W) :
    (closedImmersionComplementι i).app W ((restrictToComplement f i).app W t) =
      (closedImmersionComplementι (inverseImageι f i) ≫ f).app W t :=
  sorry

/-- The square with vertices the two complements, `Y`, and `X` commutes:
`restrictToComplement f i ≫ closedImmersionComplementι i =
closedImmersionComplementι (inverseImageι f i) ≫ f`. -/
theorem restrictToComplement_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    restrictToComplement f i ≫ closedImmersionComplementι i =
      closedImmersionComplementι (inverseImageι f i) ≫ f :=
  sorry

/-- The commutative square of complement inclusions over `f`. -/
theorem restrictToComplementCommSq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    CommSq (restrictToComplement f i) (closedImmersionComplementι (inverseImageι f i))
      (closedImmersionComplementι i) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
