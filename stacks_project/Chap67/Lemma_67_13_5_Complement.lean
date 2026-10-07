module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap66.Remark_66_19_11_StalkFunctor

/-!
# Open complement of a closed immersion of algebraic spaces

The complement `X \ Z` of a closed immersion `i : Z ⟶ X` of algebraic spaces is the
subfunctor of maps into `X` whose image of points misses `|Z|`. Restriction of sheaves
of sets to this open, and the geometric-point support condition for abelian sheaves,
are recorded here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

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
    [IsClosedImmersion i] : Subfunctor X.functorOfPoints where
  obj U := {α | missesClosedImage i α}
  map := sorry

/-- Membership in the complement subfunctor is the missing-closed-image condition. -/
theorem mem_closedImmersionComplementSubfunctor_obj {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    α ∈ (closedImmersionComplementSubfunctor i).obj U ↔ missesClosedImage i α :=
  Iff.rfl

/-- The open complement algebraic space `X \ Z` of a closed immersion `i : Z ⟶ X`. -/
def closedImmersionComplement {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    AlgebraicSpace S :=
  ofFunctor (closedImmersionComplementSubfunctor i).toFunctor sorry sorry sorry

/-- The functor of points of the complement is the missing-`|Z|` subfunctor. -/
theorem closedImmersionComplement_functorOfPoints {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionComplement i).functorOfPoints =
      (closedImmersionComplementSubfunctor i).toFunctor :=
  rfl

/-- The open immersion of the complement `X \ Z` into `X`. -/
def closedImmersionComplementι {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement i ⟶ X :=
  (closedImmersionComplementSubfunctor i).ι

/-- The complement inclusion is the subfunctor inclusion of maps missing `|Z|`. -/
theorem closedImmersionComplementι_eq {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    closedImmersionComplementι i = (closedImmersionComplementSubfunctor i).ι :=
  rfl

/-- The inclusion of the complement of a closed immersion is an open immersion. -/
instance instIsOpenImmersion_closedImmersionComplementι {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : IsOpenImmersion (closedImmersionComplementι i) :=
  sorry

namespace Etale

/-- An open immersion of algebraic spaces is étale. -/
instance ofIsOpenImmersion {X Y : AlgebraicSpace S} {f : X ⟶ Y} [IsOpenImmersion f] :
    Etale f :=
  sorry

end Etale

/-- The image of `|X \ Z|` in `|X|` is the complement of `|Z|`. -/
theorem closedImmersionComplement_range {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    pointsImage (closedImmersionComplementι i) = (pointsImage i)ᶜ :=
  sorry

/-- The complement of a closed immersion, as an open subspace of `X`. -/
def closedImmersionComplementSubspace {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : OpenSubspace X :=
  OpenSubspace.ofι (closedImmersionComplementι i)

/-- The complement space is the missing-`|Z|` subfunctor, included by an open immersion
whose image of points is the complement of `|Z|`. -/
theorem closedImmersionComplement_spec {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (closedImmersionComplement i).functorOfPoints =
        (closedImmersionComplementSubfunctor i).toFunctor ∧
      closedImmersionComplementι i = (closedImmersionComplementSubfunctor i).ι ∧
      IsOpenImmersion (closedImmersionComplementι i) ∧
      pointsImage (closedImmersionComplementι i) = (pointsImage i)ᶜ :=
  sorry

/-- A sheaf of sets on `X_étale` restricts to the terminal sheaf `*` on the open
complement `X \ Z` of a closed immersion `i : Z ⟶ X`. -/
def restrictsToTerminalOnComplement {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) : Prop :=
  Nonempty
    ((etaleRestrictionSheaf (closedImmersionComplementι i) (Type (u + 1))).obj F ≅
      ⊤_ (Sheaf (smallEtaleTopology (closedImmersionComplement i)) (Type (u + 1))))

/-- Restriction to `X \ Z` is isomorphic to `*` if and only if the restricted sheaf is
terminal. -/
theorem restrictsToTerminalOnComplement_iff {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    restrictsToTerminalOnComplement i F ↔
      Nonempty
        (IsTerminal
          ((etaleRestrictionSheaf (closedImmersionComplementι i) (Type (u + 1))).obj F)) :=
  sorry

/-- An abelian sheaf on `X_étale` has support contained in `|Z|` when every geometric
point at which the inverse-image sections over `Spec(k)` are nonzero lies in the image
of `|Z|`. -/
def supportSubsetImage {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj))
        AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ xbar : GeometricPoint X,
    IsZero
        (((sheafInverseImage AddCommGrpCat.{u + 1} xbar.hom).obj F).obj.obj
          (op xbar.toFieldValuedPoint.sourceObj)) ∨
      xbar.image ∈ pointsImage i

/-- Support contained in `|Z|` means that a geometric point with nonzero inverse-image
sections over `Spec(k)` has image in `|Z|`. -/
theorem supportSubsetImage_iff {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj))
        AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    supportSubsetImage i F ↔
      ∀ xbar : GeometricPoint X,
        ¬ IsZero
            (((sheafInverseImage AddCommGrpCat.{u + 1} xbar.hom).obj F).obj.obj
              (op xbar.toFieldValuedPoint.sourceObj)) →
          xbar.image ∈ pointsImage i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
