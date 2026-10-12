/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_13_5_Complement

/-!
# Open complement of the image of an integral morphism of algebraic spaces

The complement `|X| \ f(|Y|)` of an integral morphism `f : Y ⟶ X` of algebraic spaces is
the subfunctor of maps into `X` whose image of points misses `f(|Y|)`. Restriction of
sheaves of sets to this open is recorded here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A section of the functor of points of `X` misses the image of `f` when the induced map on
points lands in the complement of `f(|Y|)`. -/
def missesImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : Prop :=
  pointsImage (homOfYonedaSection α) ⊆ (pointsImage f)ᶜ

/-- Missing the image of `f` is the point-set condition on the Yoneda morphism associated to a
section. -/
theorem missesImage_iff {X Y : AlgebraicSpace S} (f : Y ⟶ X) {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) :
    missesImage f α ↔ pointsImage (homOfYonedaSection α) ⊆ (pointsImage f)ᶜ :=
  Iff.rfl

/-- The subfunctor of maps into `X` whose image of points misses `f(|Y|)`. -/
def imageComplementSubfunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    Subfunctor X.functorOfPoints where
  obj U := {α | missesImage f α}
  map := sorry

/-- Membership in the image-complement subfunctor is the missing-image condition. -/
theorem mem_imageComplementSubfunctor_obj {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    α ∈ (imageComplementSubfunctor f).obj U ↔ missesImage f α :=
  Iff.rfl

/-- The open complement algebraic space `|X| \ f(|Y|)` of an integral morphism `f : Y ⟶ X`. -/
def imageComplement {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    AlgebraicSpace S :=
  ofFunctor (imageComplementSubfunctor f).toFunctor sorry sorry sorry

/-- The functor of points of the image complement is the missing-`f(|Y|)` subfunctor. -/
theorem imageComplement_functorOfPoints {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] :
    (imageComplement f).functorOfPoints = (imageComplementSubfunctor f).toFunctor :=
  rfl

/-- The open immersion of the image complement `|X| \ f(|Y|)` into `X`. -/
def imageComplementι {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    imageComplement f ⟶ X :=
  (imageComplementSubfunctor f).ι

/-- The image-complement inclusion is the subfunctor inclusion of maps missing `f(|Y|)`. -/
theorem imageComplementι_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    imageComplementι f = (imageComplementSubfunctor f).ι :=
  rfl

/-- The inclusion of the image complement of an integral morphism is an open immersion. -/
instance instIsOpenImmersion_imageComplementι {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] : IsOpenImmersion (imageComplementι f) :=
  sorry

/-- The image of `|Y|` along an integral morphism is a closed subset of `|X|`. -/
theorem isClosed_pointsImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    IsClosed (pointsImage f) :=
  sorry

/-- The image of the complement algebraic space in `|X|` is the complement of `f(|Y|)`. -/
theorem imageComplement_range {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    pointsImage (imageComplementι f) = (pointsImage f)ᶜ :=
  sorry

/-- The complement of the image of an integral morphism, as an open subspace of `X`. -/
def imageComplementSubspace {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    OpenSubspace X :=
  OpenSubspace.ofι (imageComplementι f)

/-- A sheaf of sets on `X_étale` restricts to the terminal sheaf `*` on the open complement
`|X| \ f(|Y|)` of an integral morphism `f : Y ⟶ X`. -/
def restrictsToTerminalOnImageComplement {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) : Prop :=
  Nonempty
    ((etaleRestrictionSheaf (imageComplementι f) (Type (u + 1))).obj F ≅
      ⊤_ (Sheaf (smallEtaleTopology (imageComplement f)) (Type (u + 1))))

/-- Restriction to `|X| \ f(|Y|)` is isomorphic to `*` if and only if the restricted sheaf is
terminal. -/
theorem restrictsToTerminalOnImageComplement_iff {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    restrictsToTerminalOnImageComplement f F ↔
      Nonempty
        (IsTerminal
          ((etaleRestrictionSheaf (imageComplementι f) (Type (u + 1))).obj F)) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
