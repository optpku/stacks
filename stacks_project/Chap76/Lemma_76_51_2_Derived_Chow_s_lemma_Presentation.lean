/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap69.Lemma_69_20_1_ProjectiveSpace
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

/-!
# Derived Chow presentations of algebraic spaces

This file packages the local projective-space diagram and supported derived module
supplied by the derived form of Chow's lemma for algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance OpenSubspace.instIsOpenImmersion {S : Scheme.{u}} {F : AlgebraicSpace S}
    (U : OpenSubspace F) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- The inclusion of a closed subspace is a closed immersion. -/
instance ClosedSubspace.instIsClosedImmersion {S : Scheme.{u}} {F : AlgebraicSpace S}
    (Z : ClosedSubspace F) : IsClosedImmersion Z.ι :=
  Z.isClosedImmersion

/-- A derived Chow presentation at `x` consists of a closed subspace of
`X ×_A ℙⁿ_A`, an open of `ℙⁿ_A`, and a pseudo-coherent derived module supported on
that closed subspace, with étale source restriction over the preimage of the open. -/
structure DerivedChowPresentation {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} (x : Points X) where
  /-- The dimension of the chosen relative projective space. -/
  n : ℕ
  /-- The closed subspace `Z ⊂ X ×_A ℙⁿ_A`. -/
  Z : ClosedSubspace (ProjectiveSpace n X)
  /-- The distinguished point of `|Z|`. -/
  z : Points Z.X
  /-- The chosen open of `ℙⁿ_A`. -/
  V : OpenSubspace (ofScheme n (Spec (CommRingCat.of A)))
  /-- The derived module on `X ×_A ℙⁿ_A`. -/
  E : ModuleDerived (ProjectiveSpace n X)
  /-- Over `X ×_A V`, the derived module is the degree-zero pushforward of `𝒪_Z`. -/
  restrictionIso :
    let ambientOpenι := openInverseImageι (ProjectiveSpace.toOfScheme n X) V.ι
    let pushforwardStructureSheaf :=
      (DerivedCategory.singleFunctor (Modules (ProjectiveSpace n X)) 0).obj
        (Hom.pushforwardStructureModule Z.ι)
    (modulePullbackDerived ambientOpenι).obj E ≅
      (modulePullbackDerived ambientOpenι).obj pushforwardStructureSheaf
  /-- The closed immersion `Z ⟶ X ×_A ℙⁿ_A` is of finite presentation. -/
  immersionFinitePresentation : FinitePresentation Z.ι
  /-- The projection `c : Z ⟶ ℙⁿ_A` is a closed immersion over `V`. -/
  isClosedImmersionOverProjectiveOpen :
    IsClosedImmersion (openInverseImageTo (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι)
  /-- The restriction of `b : Z ⟶ X` to `W = c⁻¹(V)` is étale. -/
  sourceRestrictionEtale :
    Etale (openInverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι ≫
      Z.ι ≫ ProjectiveSpace.toBase n X)
  /-- The distinguished point lies in `W = c⁻¹(V)`. -/
  pointMemPreimage :
    z ∈ Set.range (Points.map (openInverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι))
  /-- The source projection carries the distinguished point to `x`. -/
  sourceProjectionPoint : Points.map (Z.ι ≫ ProjectiveSpace.toBase n X) z = x
  /-- The derived module is pseudo-coherent. -/
  pseudoCoherent : IsPseudoCoherent (ProjectiveSpace n X) E
  /-- The derived module is supported on `Z`. -/
  supportedOn : ModuleDerived.IsSupportedOn E (Set.range (Points.map Z.ι))

namespace DerivedChowPresentation

variable {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
  {x : Points X}

/-- The ambient fibre product `X ×_A ℙⁿ_A` of a derived Chow presentation. -/
def ambient (M : DerivedChowPresentation x) : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ProjectiveSpace M.n X

/-- The canonical closed immersion of `Z` into the ambient fibre product. -/
def immersion (M : DerivedChowPresentation x) : M.Z.X ⟶ M.ambient :=
  M.Z.ι

/-- The projection `b : Z ⟶ X`. -/
def sourceProjection (M : DerivedChowPresentation x) : M.Z.X ⟶ X :=
  M.Z.ι ≫ ProjectiveSpace.toBase M.n X

/-- The projection `c : Z ⟶ ℙⁿ_A`. -/
def projectiveProjection (M : DerivedChowPresentation x) :
    M.Z.X ⟶ ofScheme M.n (Spec (CommRingCat.of A)) :=
  M.Z.ι ≫ ProjectiveSpace.toOfScheme M.n X

/-- The open preimage `W = c⁻¹(V)` in `Z`. -/
def preimage (M : DerivedChowPresentation x) : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  openInverseImage M.projectiveProjection M.V.ι

/-- The open immersion `W ⟶ Z`. -/
def preimageι (M : DerivedChowPresentation x) : M.preimage ⟶ M.Z.X :=
  openInverseImageι M.projectiveProjection M.V.ι

/-- The comparison morphism `W ⟶ V`. -/
def preimageTo (M : DerivedChowPresentation x) : M.preimage ⟶ M.V.X :=
  openInverseImageTo M.projectiveProjection M.V.ι

/-- The open `X ×_A V` of the ambient fibre product. -/
def ambientOpen (M : DerivedChowPresentation x) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  openInverseImage (ProjectiveSpace.toOfScheme M.n X) M.V.ι

/-- The open immersion `X ×_A V ⟶ X ×_A ℙⁿ_A`. -/
def ambientOpenι (M : DerivedChowPresentation x) : M.ambientOpen ⟶ M.ambient :=
  openInverseImageι (ProjectiveSpace.toOfScheme M.n X) M.V.ι

/-- The underived pushforward `(b, c)_* 𝒪_Z`, placed in degree zero in `D(𝒪)`. -/
def pushforwardStructureSheaf (M : DerivedChowPresentation x) : ModuleDerived M.ambient :=
  (DerivedCategory.singleFunctor (Modules M.ambient) 0).obj
    (Hom.pushforwardStructureModule M.Z.ι)

/-- Constructs a derived Chow presentation from an explicit closed-subspace diagram,
its local projection properties, and a supported pseudo-coherent derived module. -/
def ofComponents (n : ℕ) (Z : ClosedSubspace (ProjectiveSpace n X)) (z : Points Z.X)
    (V : OpenSubspace (ofScheme n (Spec (CommRingCat.of A))))
    (E : ModuleDerived (ProjectiveSpace n X))
    (restrictionIso :
      let ambientOpenι := openInverseImageι (ProjectiveSpace.toOfScheme n X) V.ι
      let pushforwardStructureSheaf :=
        (DerivedCategory.singleFunctor (Modules (ProjectiveSpace n X)) 0).obj
          (Hom.pushforwardStructureModule Z.ι)
      (modulePullbackDerived ambientOpenι).obj E ≅
        (modulePullbackDerived ambientOpenι).obj pushforwardStructureSheaf)
    (immersionFinitePresentation : FinitePresentation Z.ι)
    (isClosedImmersionOverProjectiveOpen :
      IsClosedImmersion (openInverseImageTo (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι))
    (sourceRestrictionEtale :
      Etale (openInverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι ≫
        Z.ι ≫ ProjectiveSpace.toBase n X))
    (pointMemPreimage :
      z ∈ Set.range
        (Points.map (openInverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι)))
    (sourceProjectionPoint : Points.map (Z.ι ≫ ProjectiveSpace.toBase n X) z = x)
    (pseudoCoherent : IsPseudoCoherent (ProjectiveSpace n X) E)
    (supportedOn : ModuleDerived.IsSupportedOn E (Set.range (Points.map Z.ι))) :
    DerivedChowPresentation x where
  n := n
  Z := Z
  z := z
  V := V
  E := E
  restrictionIso := restrictionIso
  immersionFinitePresentation := immersionFinitePresentation
  isClosedImmersionOverProjectiveOpen := isClosedImmersionOverProjectiveOpen
  sourceRestrictionEtale := sourceRestrictionEtale
  pointMemPreimage := pointMemPreimage
  sourceProjectionPoint := sourceProjectionPoint
  pseudoCoherent := pseudoCoherent
  supportedOn := supportedOn

/-- The defining conditions of a derived Chow presentation are finite presentation of
the closed immersion, a closed immersion over `V`, étale source restriction on
`W = c⁻¹(V)`, the stated point conditions, the restriction isomorphism, and a
supported pseudo-coherent derived module. -/
theorem conditions_spec (M : DerivedChowPresentation x) :
    FinitePresentation M.Z.ι ∧
      IsClosedImmersion M.preimageTo ∧
      Etale (M.preimageι ≫ M.sourceProjection) ∧
      M.z ∈ Set.range (Points.map M.preimageι) ∧
      Points.map M.sourceProjection M.z = x ∧
      Nonempty
        ((modulePullbackDerived M.ambientOpenι).obj M.E ≅
          (modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf) ∧
      IsPseudoCoherent M.ambient M.E ∧
      ModuleDerived.IsSupportedOn M.E (Set.range (Points.map M.Z.ι)) := sorry

end DerivedChowPresentation

end AlgebraicGeometry.AlgebraicSpace
