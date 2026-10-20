module

public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.ChowGroup.Codimension
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import Mathlib.Data.Part

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom.VirtualNormalBundle

/-- Open subschemes in a Gysin test remain locally of finite type over the base. -/
instance openOverLocallyOfFiniteType {S : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    LocallyOfFiniteType (ComponentRestriction.over X U).hom :=
  ComponentRestriction.locallyOfFiniteTypeOver X U

/-- Restrict a codimension-zero class to an open in its dimension-`n` stratum. -/
def restrictClass {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X W : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType W.hom]
    (D : X.hom.GenericDimensionStratification δ) (n : ℤ)
    (j : W ⟶ ComponentRestriction.over X (D.stratum n)) [IsOpenImmersion j.left]
    (α : ChowGroup.Codimension D 0) : RelativeChow δ W n :=
  RelativeChow.castDegree δ ((add_zero (n - 0)).trans (sub_zero n))
    (@ChowGroup.flatPullback S inferInstance δ inferInstance W
      (ComponentRestriction.over X (D.stratum n)) inferInstance inferInstance j 0
      inferInstance (Scheme.Hom.relativeDimension_zero_of_isOpenImmersion j.left)
      (n - 0) (α n))

/-- Restriction of the full fundamental class is the homogeneous fundamental class
on an open of a single generic-dimension stratum. -/
theorem restrictClass_fundamentalClass {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X W : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType W.hom]
    (D : X.hom.GenericDimensionStratification δ) (n : ℤ)
    (j : W ⟶ ComponentRestriction.over X (D.stratum n)) [IsOpenImmersion j.left] :
    restrictClass δ D n j (ChowGroup.Codimension.fundamentalClass D) =
      RelativeChow.fundamentalClass δ W n := sorry

/-- Geometric descent specification for the full Gysin image. On every open test square,
every immersion–smooth presentation computes the image by its integer-degree coefficients.
The other coefficients must vanish: this specifies the full action, including its grading,
rather than just a projection to codimension zero. Presentations and deformation models are
test data, not hypotheses on the original morphism. -/
def IsImage {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (α : ChowGroup.Codimension DY 0) (β : ChowGroup.Codimension DX 0) : Prop :=
  ∀ (A B C E P : Over S)
    [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
    [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType P.hom]
    (jA : A ⟶ X) [IsOpenImmersion jA.left]
    (jB : B ⟶ Y) [IsOpenImmersion jB.left]
    (n m : ℤ)
    (jC : C ⟶ ComponentRestriction.over X' (DX.stratum n))
    [IsOpenImmersion jC.left]
    (jE : E ⟶ ComponentRestriction.over Y' (DY.stratum m))
    [IsOpenImmersion jE.left]
    (f₀ : A ⟶ B) (i₀ : C ⟶ A) (f₀' : C ⟶ E) (g₀ : E ⟶ B)
    [LocallyOfFiniteType g₀.left],
    f₀ ≫ jB = jA ≫ f →
    i₀ ≫ jA = jC ≫ ComponentRestriction.ι X' (DX.stratum n) ≫ i →
    f₀' ≫ jE ≫ ComponentRestriction.ι Y' (DY.stratum m) =
      jC ≫ ComponentRestriction.ι X' (DX.stratum n) ≫ f' →
    g₀ ≫ jB = jE ≫ ComponentRestriction.ι Y' (DY.stratum m) ≫ g →
    ∀ (square₀ : IsPullback i₀.left f₀'.left f₀.left g₀.left)
      (ι : A ⟶ P) (σ : P ⟶ B) [IsRegularImmersion ι.left] [Smooth σ.left]
      (hfac : ι ≫ σ = f₀)
      (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
        Scheme.Hom.conormalSheaf ι.left)
      (D : ClosedDeformation A.hom (ι.left.coborderRange.ι ≫ P.hom)
        ι.left.liftCoborder
        ((Category.assoc ι.left.liftCoborder ι.left.coborderRange.ι P.hom).symm.trans
          ((congrArg (fun k ↦ k ≫ P.hom) ι.left.liftCoborder_ι).trans (Over.w ι)))
        (normalBundle ι.left e).toCoborder)
      (p : ℤ),
      if p = m - n then
        HEq ((factorizationClassDegree δ f₀ ι σ hfac e D p).cap i₀ f₀' g₀ square₀ m
          (restrictClass δ DY m jE α)) (restrictClass δ DX n jC β)
      else
        (factorizationClassDegree δ f₀ ι σ hfac e D p).cap i₀ f₀' g₀ square₀ m
          (restrictClass δ DY m jE α) = 0

/-- The Gysin action defined by unique geometric descent. Its domain asserts that all local
geometric computations glue to a unique full codimension-zero class. The value is selected
only from a supplied domain witness. -/
def cap {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (α : ChowGroup.Codimension DY 0) : Part (ChowGroup.Codimension DX 0) where
  Dom := ∃! β, IsImage δ f i f' g DX DY α β
  get h := Classical.choose h

/-- A defined value of the Gysin action is characterized by local geometric descent
and uniqueness. Clients need not unfold the selection of the unique class. -/
theorem cap_eq_some_iff {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (α : ChowGroup.Codimension DY 0) (β : ChowGroup.Codimension DX 0) :
    cap δ f i f' g DX DY α = Part.some β ↔
      IsImage δ f i f' g DX DY α β ∧
        ∀ γ, IsImage δ f i f' g DX DY α γ → γ = β := sorry


end AlgebraicGeometry.BivariantClass.Gysin
