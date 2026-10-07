module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.Resolution.Computation

@[expose] public section

/-!
# Naturality of resolution Ext computations

This leaf records the pointwise source and target naturality of the canonical shift transports.
It deliberately does not choose a category of resolutions: the resolution structures in this
project carry a comparison map but no bundled morphism between two choices.  Such comparisons are
therefore expressed below by an explicit compatibility equation.
-/

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open scoped DerivedExt

noncomputable section

universe w v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

namespace IsKInjective

/-! ### Inverse K-injective Hom transport -/

/-- Stacks 070I: the inverse K-injective Hom equivalence is contravariantly natural in its
homotopy source. -/
@[stacks 070I "inverse K-injective Hom naturality in the source"]
theorem homAddEquiv_symm_naturality_left
    {M M' : HomotopyCategory 𝒜 (up ℤ)} (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (f : M' ⟶ M)
    (α : DerivedCategory.Qh.obj M ⟶ DerivedCategory.Qh.obj ((KQ).obj I)) :
    (homAddEquiv M' I).symm (DerivedCategory.Qh.map f ≫ α) =
      f ≫ (homAddEquiv M I).symm α := sorry

/-- Stacks 070I: the inverse K-injective Hom equivalence is covariantly natural in its
K-injective target. -/
@[stacks 070I "inverse K-injective Hom naturality in the target"]
theorem homAddEquiv_symm_naturality_right
    (M : HomotopyCategory 𝒜 (up ℤ)) (I J : CochainComplex 𝒜 ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (α : DerivedCategory.Qh.obj M ⟶ DerivedCategory.Qh.obj ((KQ).obj I))
    (g : (KQ).obj I ⟶ (KQ).obj J) :
    (homAddEquiv M J).symm (α ≫ DerivedCategory.Qh.map g) =
      (homAddEquiv M I).symm α ≫ g := sorry

end IsKInjective

namespace IsKProjective

/-! ### Inverse K-projective Hom transport -/

/-- Stacks 064B: the inverse K-projective Hom equivalence is contravariantly natural in its
K-projective source. -/
@[stacks 064B "inverse K-projective Hom naturality in the source"]
theorem homAddEquiv_symm_naturality_left
    (P P' : CochainComplex 𝒜 ℤ) (K : HomotopyCategory 𝒜 (up ℤ))
    [P.IsKProjective] [P'.IsKProjective]
    (f : (KQ).obj P ⟶ (KQ).obj P')
    (α : DerivedCategory.Qh.obj ((KQ).obj P') ⟶ DerivedCategory.Qh.obj K) :
    (homAddEquiv P K).symm (DerivedCategory.Qh.map f ≫ α) =
      f ≫ (homAddEquiv P' K).symm α := sorry

/-- Stacks 064B: the inverse K-projective Hom equivalence is covariantly natural in its target. -/
@[stacks 064B "inverse K-projective Hom naturality in the target"]
theorem homAddEquiv_symm_naturality_right
    (P : CochainComplex 𝒜 ℤ) (K K' : HomotopyCategory 𝒜 (up ℤ)) [P.IsKProjective]
    (α : DerivedCategory.Qh.obj ((KQ).obj P) ⟶ DerivedCategory.Qh.obj K)
    (g : K ⟶ K') :
    (homAddEquiv P K').symm (α ≫ DerivedCategory.Qh.map g) =
      (homAddEquiv P K).symm α ≫ g := sorry

end IsKProjective

namespace Resolution

/-! ### Derived shift comparison -/

/-- Stacks 06XR: `shiftAddEquiv` is contravariantly natural in the source complex. -/
@[stacks 06XR "source naturality of the derived shift comparison"]
theorem shiftAddEquiv_naturality_left
    {X X' Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    shiftAddEquiv X' Y i (Q.map f ≫ α) =
      Q.map f ≫ shiftAddEquiv X Y i α := sorry

/-- Stacks 06XR: `shiftAddEquiv` is covariantly natural in the target complex. -/
@[stacks 06XR "target naturality of the derived shift comparison"]
theorem shiftAddEquiv_naturality_right
    {X Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    shiftAddEquiv X Y' i (α ≫ (Q.map g)⟦i⟧') =
      shiftAddEquiv X Y i α ≫ Q.map (g⟦i⟧') := sorry

/-- Stacks 06XR: the inverse derived shift comparison is contravariantly natural in the source.
-/
@[stacks 06XR "inverse source naturality of the derived shift comparison"]
theorem shiftAddEquiv_symm_naturality_left
    {X X' Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    (shiftAddEquiv X' Y i).symm (Q.map f ≫ α) =
      Q.map f ≫ (shiftAddEquiv X Y i).symm α := sorry

/-- Stacks 06XR: the inverse derived shift comparison is covariantly natural in the target.
-/
@[stacks 06XR "inverse target naturality of the derived shift comparison"]
theorem shiftAddEquiv_symm_naturality_right
    {X Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    (shiftAddEquiv X Y' i).symm (α ≫ Q.map (g⟦i⟧')) =
      (shiftAddEquiv X Y i).symm α ≫ (Q.map g)⟦i⟧' := sorry

/-! ### Homotopy-category shift comparison -/

/-- Stacks 06XR: `shiftedHomAddEquiv` is contravariantly natural in the source complex. -/
@[stacks 06XR "source naturality of the homotopy shift comparison"]
theorem shiftedHomAddEquiv_naturality_left
    {X X' Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : (KQ).obj X ⟶ (KQ).obj (Y⟦i⟧)) :
    shiftedHomAddEquiv X' Y i
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f ≫ α) =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map f ≫ shiftedHomAddEquiv X Y i α := sorry

/-- Stacks 06XR: `shiftedHomAddEquiv` is covariantly natural in the target complex. -/
@[stacks 06XR "target naturality of the homotopy shift comparison"]
theorem shiftedHomAddEquiv_naturality_right
    {X Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : (KQ).obj X ⟶ (KQ).obj (Y⟦i⟧)) :
    shiftedHomAddEquiv X Y' i
        (α ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map (g⟦i⟧')) =
      shiftedHomAddEquiv X Y i α ≫
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map g)⟦i⟧' := sorry

/-- Stacks 06XR: the inverse homotopy shift comparison is contravariantly natural in the source.
-/
@[stacks 06XR "inverse source naturality of the homotopy shift comparison"]
theorem shiftedHomAddEquiv_symm_naturality_left
    {X X' Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : Ext⁽i⁾((KQ).obj X, (KQ).obj Y)) :
    (shiftedHomAddEquiv X' Y i).symm
        (((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫ α) =
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
        (shiftedHomAddEquiv X Y i).symm α := sorry

/-- Stacks 06XR: the inverse homotopy shift comparison is covariantly natural in the target.
-/
@[stacks 06XR "inverse target naturality of the homotopy shift comparison"]
theorem shiftedHomAddEquiv_symm_naturality_right
    {X Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Ext⁽i⁾((KQ).obj X, (KQ).obj Y)) :
    (shiftedHomAddEquiv X Y' i).symm
        (α ≫ ((HomotopyCategory.quotient 𝒜 (up ℤ)).map g)⟦i⟧') =
      (shiftedHomAddEquiv X Y i).symm α ≫
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map (g⟦i⟧')) := sorry

end Resolution

namespace InjectiveResolution

variable {Y : CochainComplex 𝒜 ℤ}

/-! ### Injective-resolution transports -/

/-- Stacks 06XR: the injective resolution transport is contravariantly natural in the source. -/
@[stacks 06XR "source naturality of injective resolution transport"]
theorem resolutionAddEquiv_naturality_left
    (I : InjectiveResolution Y) {X X' : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    resolutionAddEquiv I X' i (Q.map f ≫ α) =
      Q.map f ≫ resolutionAddEquiv I X i α := sorry

/-- Stacks 06XR: inverse source naturality for injective resolution transport. -/
@[stacks 06XR "inverse source naturality of injective resolution transport"]
theorem resolutionAddEquiv_symm_naturality_left
    (I : InjectiveResolution Y) {X X' : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (β : Q.obj X ⟶ Q.obj (I⟦i⟧)) :
    (resolutionAddEquiv I X' i).symm (Q.map f ≫ β) =
      Q.map f ≫ (resolutionAddEquiv I X i).symm β := sorry

/-- Stacks 06XR: the injective homotopy transport is contravariantly natural in the source. -/
@[stacks 06XR "source naturality of injective homotopy transport"]
theorem homotopyAddEquiv_naturality_left
    (I : InjectiveResolution Y) {X X' : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (I⟦i⟧)) :
    homotopyAddEquiv I X' i (Q.map f ≫ α) =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map f ≫ homotopyAddEquiv I X i α := sorry

/-- Stacks 06XR: inverse source naturality for injective homotopy transport. -/
@[stacks 06XR "inverse source naturality of injective homotopy transport"]
theorem homotopyAddEquiv_symm_naturality_left
    (I : InjectiveResolution Y) {X X' : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (β : (KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) :
    (homotopyAddEquiv I X' i).symm
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f ≫ β) =
      Q.map f ≫ (homotopyAddEquiv I X i).symm β := sorry

/-- Stacks 06XR: compatible maps of injective resolutions commute with target transport.

The explicit equation `hι` is intentional: the project has no bundled category of chosen
injective resolutions, so this bridge does not hide a noncanonical resolution morphism. -/
@[stacks 06XR "target naturality of injective resolution transport"]
theorem resolutionAddEquiv_naturality_right
    {Y Y' : CochainComplex 𝒜 ℤ} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y')
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ))
    (hι : I.ι ≫ h = g ≫ J.ι) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    resolutionAddEquiv J X i (α ≫ Q.map (g⟦i⟧')) =
      resolutionAddEquiv I X i α ≫ Q.map (h⟦i⟧') := sorry

/-- Stacks 06XR: inverse target naturality for compatible injective resolution transports.

The input is written through the forward transport on `I`; this is the canonical inverse form
and does not require the comparison map `h` to be chosen as an inverse. -/
@[stacks 06XR "inverse target naturality of injective resolution transport"]
theorem resolutionAddEquiv_symm_naturality_right
    {Y Y' : CochainComplex 𝒜 ℤ} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y')
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ))
    (hι : I.ι ≫ h = g ≫ J.ι) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    (resolutionAddEquiv J X i).symm
        (resolutionAddEquiv I X i α ≫ Q.map (h⟦i⟧')) =
      α ≫ Q.map (g⟦i⟧') := sorry

/-- Stacks 06XR: the injective homotopy transport is natural in a map of resolving complexes. -/
@[stacks 06XR "target naturality of injective homotopy transport"]
theorem homotopyAddEquiv_naturality_right
    {Y Y' : CochainComplex 𝒜 ℤ} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : CochainComplex 𝒜 ℤ}
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ)) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (I⟦i⟧)) :
    homotopyAddEquiv J X i (α ≫ Q.map (h⟦i⟧')) =
      homotopyAddEquiv I X i α ≫
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map (h⟦i⟧') := sorry

/-- Stacks 06XR: inverse target naturality for compatible injective homotopy transports. -/
@[stacks 06XR "inverse target naturality of injective homotopy transport"]
theorem homotopyAddEquiv_symm_naturality_right
    {Y Y' : CochainComplex 𝒜 ℤ} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : CochainComplex 𝒜 ℤ}
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ)) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (I⟦i⟧)) :
    (homotopyAddEquiv J X i).symm
        (homotopyAddEquiv I X i α ≫
          (HomotopyCategory.quotient 𝒜 (up ℤ)).map (h⟦i⟧')) =
      α ≫ Q.map (h⟦i⟧') := sorry

/-- Stacks 06XR: the full injective-resolution Ext equivalence is source-natural. -/
@[stacks 06XR "source naturality of injective Ext computation"]
theorem extAddEquiv_naturality_left
    (I : InjectiveResolution Y) {X X' : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    I.extAddEquiv X' i (Q.map f ≫ α) =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map f ≫ I.extAddEquiv X i α := sorry

/-- Stacks 06XR: inverse source naturality for injective Ext computation. -/
@[stacks 06XR "inverse source naturality of injective Ext computation"]
theorem extAddEquiv_symm_naturality_left
    (I : InjectiveResolution Y) {X X' : CochainComplex 𝒜 ℤ} (f : X' ⟶ X) (i : ℤ)
    (β : Ext⁽i⁾((KQ).obj X, (KQ).obj I)) :
    (I.extAddEquiv X' i).symm
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f ≫ β) =
      Q.map f ≫ (I.extAddEquiv X i).symm β := sorry

/-- Stacks 06XR: compatible maps of injective resolutions induce target-natural Ext computation. -/
@[stacks 06XR "target naturality of injective Ext computation"]
theorem extAddEquiv_naturality_right
    {Y Y' : CochainComplex 𝒜 ℤ} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y')
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ))
    (hι : I.ι ≫ h = g ≫ J.ι) (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    J.extAddEquiv X i (α ≫ (Q.map g)⟦i⟧') =
      I.extAddEquiv X i α ≫
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h)⟦i⟧' := sorry

/-- Stacks 06XR: inverse target naturality for compatible injective Ext computations. -/
@[stacks 06XR "inverse target naturality of injective Ext computation"]
theorem extAddEquiv_symm_naturality_right
    {Y Y' : CochainComplex 𝒜 ℤ} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    {X : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y')
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ))
    (hι : I.ι ≫ h = g ≫ J.ι) (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    (J.extAddEquiv X i).symm
        (I.extAddEquiv X i α ≫
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h)⟦i⟧') =
      α ≫ (Q.map g)⟦i⟧' := sorry

/-- Stacks 06XR: Ext computations made with two injective resolutions of the same complex agree
after transport along any compatible comparison map.  This identity specialization of
`extAddEquiv_naturality_right` avoids exposing shifted identity maps at use sites. -/
@[stacks 06XR "comparison invariance of injective Ext computation"]
theorem extAddEquiv_comparison
    (I J : InjectiveResolution Y) {X : CochainComplex 𝒜 ℤ}
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ))
    (hι : I.ι ≫ h = J.ι) (i : ℤ) (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    J.extAddEquiv X i α =
      I.extAddEquiv X i α ≫
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h)⟦i⟧' := sorry

/-- Stacks 06XR: inverse comparison invariance for injective Ext computation. -/
@[stacks 06XR "inverse comparison invariance of injective Ext computation"]
theorem extAddEquiv_comparison_symm
    (I J : InjectiveResolution Y) {X : CochainComplex 𝒜 ℤ}
    (h : (I : CochainComplex 𝒜 ℤ) ⟶ (J : CochainComplex 𝒜 ℤ))
    (hι : I.ι ≫ h = J.ι) (i : ℤ) (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    (J.extAddEquiv X i).symm
        (I.extAddEquiv X i α ≫
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h)⟦i⟧') = α := sorry

end InjectiveResolution

namespace ProjectiveResolution

variable {X : CochainComplex 𝒜 ℤ}

/-! ### Projective-resolution transports -/

/-- Stacks 06XR: the projective resolution transport is covariantly natural in the target. -/
@[stacks 06XR "target naturality of projective resolution transport"]
theorem resolutionAddEquiv_naturality_right
    (P : ProjectiveResolution X) {Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    resolutionAddEquiv P Y' i (α ≫ Q.map (g⟦i⟧')) =
      resolutionAddEquiv P Y i α ≫ Q.map (g⟦i⟧') := sorry

/-- Stacks 06XR: inverse target naturality for projective resolution transport. -/
@[stacks 06XR "inverse target naturality of projective resolution transport"]
theorem resolutionAddEquiv_symm_naturality_right
    (P : ProjectiveResolution X) {Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (β : Q.obj (P : CochainComplex 𝒜 ℤ) ⟶ Q.obj (Y⟦i⟧)) :
    (resolutionAddEquiv P Y' i).symm (β ≫ Q.map (g⟦i⟧')) =
      (resolutionAddEquiv P Y i).symm β ≫ Q.map (g⟦i⟧') := sorry

/-- Stacks 06XR: the projective homotopy transport is covariantly natural in the target. -/
@[stacks 06XR "target naturality of projective homotopy transport"]
theorem homotopyAddEquiv_naturality_right
    (P : ProjectiveResolution X) {Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Q.obj (P : CochainComplex 𝒜 ℤ) ⟶ Q.obj (Y⟦i⟧)) :
    homotopyAddEquiv P Y' i (α ≫ Q.map (g⟦i⟧')) =
      homotopyAddEquiv P Y i α ≫
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map (g⟦i⟧') := sorry

/-- Stacks 06XR: inverse target naturality for projective homotopy transport. -/
@[stacks 06XR "inverse target naturality of projective homotopy transport"]
theorem homotopyAddEquiv_symm_naturality_right
    (P : ProjectiveResolution X) {Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (β : (KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) :
    (homotopyAddEquiv P Y' i).symm
        (β ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map (g⟦i⟧')) =
      (homotopyAddEquiv P Y i).symm β ≫ Q.map (g⟦i⟧') := sorry

/-- Stacks 06XR: compatible maps of projective resolutions commute with source transport.

As for injective resolutions, `hπ` keeps the chosen comparison equation explicit rather than
introducing a noncanonical morphism object. -/
@[stacks 06XR "source naturality of projective resolution transport"]
theorem resolutionAddEquiv_naturality_left
    {X X' : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    {Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X)
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ))
    (hπ : h ≫ P.π = P'.π ≫ f) (i : ℤ)
    (α : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    resolutionAddEquiv P' Y i (Q.map f ≫ α) =
      Q.map h ≫ resolutionAddEquiv P Y i α := sorry

/-- Stacks 06XR: inverse source naturality for compatible projective resolution transports.

The input is written through the forward transport on `P`; no inverse comparison map is
required. -/
@[stacks 06XR "inverse source naturality of projective resolution transport"]
theorem resolutionAddEquiv_symm_naturality_left
    {X X' : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    {Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X)
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ))
    (hπ : h ≫ P.π = P'.π ≫ f) (i : ℤ)
    (β : Q.obj (P : CochainComplex 𝒜 ℤ) ⟶ Q.obj (Y⟦i⟧)) :
    (resolutionAddEquiv P' Y i).symm
        (Q.map h ≫ β) =
      Q.map f ≫ (resolutionAddEquiv P Y i).symm β := sorry

/-- Stacks 06XR: the projective homotopy transport is natural in a map of resolving complexes. -/
@[stacks 06XR "source naturality of projective homotopy transport"]
theorem homotopyAddEquiv_naturality_left
    {X X' : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    {Y : CochainComplex 𝒜 ℤ}
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ)) (i : ℤ)
    (α : Q.obj (P : CochainComplex 𝒜 ℤ) ⟶ Q.obj (Y⟦i⟧)) :
    homotopyAddEquiv P' Y i (Q.map h ≫ α) =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map h ≫ homotopyAddEquiv P Y i α := sorry

/-- Stacks 06XR: inverse source naturality for compatible projective homotopy transports. -/
@[stacks 06XR "inverse source naturality of projective homotopy transport"]
theorem homotopyAddEquiv_symm_naturality_left
    {X X' : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    {Y : CochainComplex 𝒜 ℤ}
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ)) (i : ℤ)
    (β : (KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) :
    (homotopyAddEquiv P' Y i).symm
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h ≫ β) =
      Q.map h ≫ (homotopyAddEquiv P Y i).symm β := sorry

/-- Stacks 06XR: the full projective-resolution Ext equivalence is target-natural. -/
@[stacks 06XR "target naturality of projective Ext computation"]
theorem extAddEquiv_naturality_right
    (P : ProjectiveResolution X) {Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    P.extAddEquiv Y' i (α ≫ (Q.map g)⟦i⟧') =
      P.extAddEquiv Y i α ≫
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map g)⟦i⟧' := sorry

/-- Stacks 06XR: inverse target naturality for projective Ext computation. -/
@[stacks 06XR "inverse target naturality of projective Ext computation"]
theorem extAddEquiv_symm_naturality_right
    (P : ProjectiveResolution X) {Y Y' : CochainComplex 𝒜 ℤ} (g : Y ⟶ Y') (i : ℤ)
    (α : Ext⁽i⁾((KQ).obj P, (KQ).obj Y)) :
    (P.extAddEquiv Y' i).symm
        (α ≫ ((HomotopyCategory.quotient 𝒜 (up ℤ)).map g)⟦i⟧') =
      (P.extAddEquiv Y i).symm α ≫ (Q.map g)⟦i⟧' := sorry

/-- Stacks 06XR: compatible maps of projective resolutions induce source-natural Ext computation. -/
@[stacks 06XR "source naturality of projective Ext computation"]
theorem extAddEquiv_naturality_left
    {X X' : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    {Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X)
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ))
    (hπ : h ≫ P.π = P'.π ≫ f) (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    P'.extAddEquiv Y i (Q.map f ≫ α) =
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h) ≫ P.extAddEquiv Y i α := sorry

/-- Stacks 06XR: inverse source naturality for compatible projective Ext computations. -/
@[stacks 06XR "inverse source naturality of projective Ext computation"]
theorem extAddEquiv_symm_naturality_left
    {X X' : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    {Y : CochainComplex 𝒜 ℤ} (f : X' ⟶ X)
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ))
    (hπ : h ≫ P.π = P'.π ≫ f) (i : ℤ)
    (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    (P'.extAddEquiv Y i).symm
        (((HomotopyCategory.quotient 𝒜 (up ℤ)).map h) ≫ P.extAddEquiv Y i α) =
      Q.map f ≫ α := sorry

/-- Stacks 06XR: Ext computations made with two projective resolutions of the same complex agree
after transport along any compatible comparison map.  This identity specialization of
`extAddEquiv_naturality_left` avoids exposing localized identity maps at use sites. -/
@[stacks 06XR "comparison invariance of projective Ext computation"]
theorem extAddEquiv_comparison
    (P P' : ProjectiveResolution X) {Y : CochainComplex 𝒜 ℤ}
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ))
    (hπ : h ≫ P.π = P'.π) (i : ℤ) (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    P'.extAddEquiv Y i α =
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map h) ≫ P.extAddEquiv Y i α := sorry

/-- Stacks 06XR: inverse comparison invariance for projective Ext computation. -/
@[stacks 06XR "inverse comparison invariance of projective Ext computation"]
theorem extAddEquiv_comparison_symm
    (P P' : ProjectiveResolution X) {Y : CochainComplex 𝒜 ℤ}
    (h : (P' : CochainComplex 𝒜 ℤ) ⟶ (P : CochainComplex 𝒜 ℤ))
    (hπ : h ≫ P.π = P'.π) (i : ℤ) (α : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    (P'.extAddEquiv Y i).symm
        (((HomotopyCategory.quotient 𝒜 (up ℤ)).map h) ≫ P.extAddEquiv Y i α) = α := sorry

end ProjectiveResolution

end

end CochainComplex
