/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback

/-!
# Derived Chow presentations of algebraic spaces

A derived Chow presentation combines a local projective-space diagram with a
supported pseudo-coherent derived module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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
    let ambientOpenι := Open.inverseImageι (ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf
    let pushforwardStructureSheaf :=
      (DerivedCategory.singleFunctor (Modules (ProjectiveSpace n X)) 0).obj
        (Hom.pushforwardStructureModule Z.ι)
    (modulePullbackDerived ambientOpenι).obj E ≅
      (modulePullbackDerived ambientOpenι).obj pushforwardStructureSheaf
  /-- The closed immersion `Z ⟶ X ×_A ℙⁿ_A` is of finite presentation. -/
  immersionFinitePresentation : FinitePresentation Z.ι
  /-- The projection `c : Z ⟶ ℙⁿ_A` is a closed immersion over `V`. -/
  isClosedImmersionOverProjectiveOpen :
    IsClosedImmersion (Open.inverseImageTo (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf)
  /-- The restriction of `b : Z ⟶ X` to `W = c⁻¹(V)` is étale. -/
  sourceRestrictionEtale :
    Etale (Open.inverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf ≫
      Z.ι ≫ ProjectiveSpace.toBase n X)
  /-- The distinguished point lies in `W = c⁻¹(V)`. -/
  pointMemPreimage :
    z ∈ Set.range (Points.map (Open.inverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf))
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
  Open.inverseImage M.projectiveProjection M.V.ι M.V.isOpenImmersion.presheaf

/-- The open immersion `W ⟶ Z`. -/
def preimageι (M : DerivedChowPresentation x) : M.preimage ⟶ M.Z.X :=
  Open.inverseImageι M.projectiveProjection M.V.ι M.V.isOpenImmersion.presheaf

/-- The comparison morphism `W ⟶ V`. -/
def preimageTo (M : DerivedChowPresentation x) : M.preimage ⟶ M.V.X :=
  Open.inverseImageTo M.projectiveProjection M.V.ι M.V.isOpenImmersion.presheaf

/-- The open `X ×_A V` of the ambient fibre product. -/
def ambientOpen (M : DerivedChowPresentation x) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  Open.inverseImage (ProjectiveSpace.toOfScheme M.n X) M.V.ι M.V.isOpenImmersion.presheaf

/-- The open immersion `X ×_A V ⟶ X ×_A ℙⁿ_A`. -/
def ambientOpenι (M : DerivedChowPresentation x) : M.ambientOpen ⟶ M.ambient :=
  Open.inverseImageι (ProjectiveSpace.toOfScheme M.n X) M.V.ι M.V.isOpenImmersion.presheaf

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
      let ambientOpenι := Open.inverseImageι (ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf
      let pushforwardStructureSheaf :=
        (DerivedCategory.singleFunctor (Modules (ProjectiveSpace n X)) 0).obj
          (Hom.pushforwardStructureModule Z.ι)
      (modulePullbackDerived ambientOpenι).obj E ≅
        (modulePullbackDerived ambientOpenι).obj pushforwardStructureSheaf)
    (immersionFinitePresentation : FinitePresentation Z.ι)
    (isClosedImmersionOverProjectiveOpen :
      IsClosedImmersion (Open.inverseImageTo (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf))
    (sourceRestrictionEtale :
      Etale (Open.inverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf ≫
        Z.ι ≫ ProjectiveSpace.toBase n X))
    (pointMemPreimage :
      z ∈ Set.range
        (Points.map (Open.inverseImageι (Z.ι ≫ ProjectiveSpace.toOfScheme n X) V.ι V.isOpenImmersion.presheaf)))
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

/-- Every point of a separated finitely presented algebraic space over a ring admits
an explicit derived Chow presentation. -/
@[stacks 0CTR]
theorem exists_of_separated_finitePresentation {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Separated (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)] (x : Points X) :
    Nonempty (DerivedChowPresentation x) := sorry

end DerivedChowPresentation

end AlgebraicGeometry.AlgebraicSpace

