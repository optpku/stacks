module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_21_3_BaseChange

/-!
# Lemma 96.21.3

On a 2-cartesian square of algebraic stacks over a scheme `S`, and for
`τ` one of Zariski, étale, smooth, syntomic, or fppf, the canonical
base-change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` is an isomorphism of derived
functors, functorial in abelian sheaves and in sheaves of modules on the
associated `τ`-sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor ComplexShape
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) (τ : StandardTopology)

section AbelianDerivedBaseChange

variable [HasDerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory
    (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (abelianPushforward f τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})
      (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]

/-- Lemma 96.21.3 (1): Let `S` be a scheme. Let `τ` be one of Zariski, étale, smooth,
syntomic, or fppf. Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be 1-morphisms of algebraic
stacks over `S`, and write `Y' ×_Y X := fibreProductApex f g`,
`f' := fibreProductFst f g`, and `g' := fibreProductSnd f g` for the chosen
2-cartesian square. Then the base-change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` is an
isomorphism of derived functors, functorial in `F` in `Ab(X_τ)`. -/
@[stacks 075H]
def abelianDerivedPushforward_baseChangeIso
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    abelianDerivedPushforward f τ ⋙
        (associatedAbelianInverseImage g τ).mapDerivedCategory ≅
      (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        abelianDerivedPushforward (fibreProductFst f g) τ :=
  abelianDerivedPushforwardBaseChangeIso f g τ

/-- The labeled abelian derived base-change isomorphism equals the canonical
identification `abelianDerivedPushforwardBaseChangeIso`. -/
theorem abelianDerivedPushforward_baseChangeIso_eq
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    abelianDerivedPushforward_baseChangeIso f g τ =
      abelianDerivedPushforwardBaseChangeIso f g τ :=
  rfl

end AbelianDerivedBaseChange

section ModuleDerivedBaseChange

variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ))]
variable [HasDerivedCategory
    (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (modulePushforward f τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))
      (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (modulePushforward f τ ⋙ associatedModuleInverseImage g τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]

/-- Lemma 96.21.3 (2): Let `S` be a scheme. Let `τ` be one of Zariski, étale, smooth,
syntomic, or fppf. Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be 1-morphisms of algebraic
stacks over `S`, and write `Y' ×_Y X := fibreProductApex f g`,
`f' := fibreProductFst f g`, and `g' := fibreProductSnd f g` for the chosen
2-cartesian square. Then the base-change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` is an
isomorphism of derived functors, functorial in `F` in `Mod(X_τ, O_X)`. -/
@[stacks 075H]
def moduleDerivedPushforward_baseChangeIso
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    moduleDerivedPushforward f τ ⋙
        (associatedModuleInverseImage g τ).mapDerivedCategory ≅
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        moduleDerivedPushforward (fibreProductFst f g) τ :=
  moduleDerivedPushforwardBaseChangeIso f g τ

/-- The labeled module derived base-change isomorphism equals the canonical
identification `moduleDerivedPushforwardBaseChangeIso`. -/
theorem moduleDerivedPushforward_baseChangeIso_eq
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    moduleDerivedPushforward_baseChangeIso f g τ =
      moduleDerivedPushforwardBaseChangeIso f g τ :=
  rfl

end ModuleDerivedBaseChange

end AlgebraicGeometry.GroupoidsOver
