/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import stacks_project.Chap85.Lemma_85_17_4_Comparison
public import stacks_project.Chap85.Lemma_85_19_2_Adjunction

/-!
# Derived global-sections comparison for a hypercovering of an object

If `K` is a hypercovering of an object `X`, Lemma 85.17.4 applied to the slice
site `J.over X` and `toSliceTerminal` supplies a Leray identification
`Ra_* ⋙ RΓ(X, -) ≅ RΓ((C / K)_total, -)` and the canonical comparison
`RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor (J.over X) AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (J.over X) AddCommGrpCat.{max w u v})
      (up ℤ))]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (overSiteTotalTopology (J.over X) K.toSimplicialObject)
      AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso
      (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
        AddCommGrpCat.{max w u v})
      (up ℤ))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Leray identification `Ra_* ⋙ RΓ(X, -) ≅ RΓ((C / K)_total, -)` for a
hypercovering of an object. -/
abbrev rGammaDirectImageIso :
    directImageDerived J X K ⋙
      RightDerived.Cochain.functor
        (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v}) ≅
    RightDerived.Cochain.functor
      (Sheaf.Γ (overSiteTotalTopology (J.over X) K.toSimplicialObject)
        AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.rGammaDirectImageIso.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- `rGammaDirectImageIso` is the slice instantiation of the terminal-hypercovering
Leray identification. -/
theorem rGammaDirectImageIso_eq :
    rGammaDirectImageIso J X K =
      SemiRepresentableFamily.rGammaDirectImageIso.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- Canonical comparison `RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)` for a
hypercovering of an object. -/
abbrev rGammaInverseImageComparison :
    RightDerived.Cochain.functor
        (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v}) ⟶
      inverseImageDerived J X K ⋙
        RightDerived.Cochain.functor
          (Sheaf.Γ (overSiteTotalTopology (J.over X) K.toSimplicialObject)
            AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.rGammaInverseImageComparison.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- `rGammaInverseImageComparison` is the derived unit of `a⁻¹ ⊣ Ra_*`, reassociated
and postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaInverseImageComparison_eq :
    rGammaInverseImageComparison J X K =
      whiskerRight (derivedUnit J X K)
          (RightDerived.Cochain.functor
            (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v})) ≫
        (associator (inverseImageDerived J X K) (directImageDerived J X K)
            (RightDerived.Cochain.functor
              (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v}))).hom ≫
        whiskerLeft (inverseImageDerived J X K)
          (rGammaDirectImageIso J X K).hom :=
  sorry

/-- The component of `rGammaInverseImageComparison` at `E` is
`RΓ(X, E) ⟶ RΓ((C / K)_total, a⁻¹ E)`. -/
theorem rGammaInverseImageComparison_app
    (E : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) :
    (rGammaInverseImageComparison J X K).app E =
      (RightDerived.Cochain.functor
            (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v})).map
          ((derivedUnit J X K).app E) ≫
        (rGammaDirectImageIso J X K).hom.app
          ((inverseImageDerived J X K).obj E) :=
  sorry


end CategoryTheory.Hypercovering
