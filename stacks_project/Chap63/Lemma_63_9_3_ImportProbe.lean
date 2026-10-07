module

public import Mathlib.CategoryTheory.Functor.Category
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_4_3
public import stacks_project.Chap63.Lemma_63_8_2_Comparison
public import stacks_project.Chap63.Lemma_63_8_3_Comp
public import stacks_project.Chap63.Lemma_63_9_3_Compactification

/-!
# Associativity of derived étale lower shriek composition

The two whiskered paths of Lemma 63.9.2 comparisons attached to a triple
of separated finite-type morphisms agree: `γ_{A+B} ∘ γ_C = γ_{B+C} ∘ γ_A`.
The four arrows are the Lemma 63.9.2 identifications on the rectangles
`C`, `A`, `A+B`, and `B+C` of one compactification tower, reconstructed as
the associator / whisker / squareMap / shriekComp / pushforwardCompIso
pasting because `Lemma_63_9_2_Comparison` does not currently elaborate.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

section ExtensionIso
variable {U T : Scheme.{u}} (j : U ⟶ T) [Etale j] [LocallyQuasiFinite j]
variable (Λ₀ : Type u) [CommRing Λ₀]
variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [T.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [T.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ₀,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]

/-- Forgetting coefficients identifies étale extension by zero of a sheaf of
`Λ`-modules with abelian extension by zero of the underlying abelian sheaf. -/
def extensionByZero_compSheafCompose
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ₀)) :
    (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})).obj
        ((etaleExtensionByZero j (ModuleCat.{u} Λ₀)).obj F) ≅
      (abelianExtensionByZero j).obj
        ((sheafCompose U.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})).obj F) :=
  (Functor.sheafPullback.compSheafComposeIso
      (etaleRestriction j) (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})
      U.smallEtaleTopology T.smallEtaleTopology).app F

/-- The component of the sheaf-level identification of étale extension by zero
with finite-support lower shriek. -/
def extensionByZeroIsoLowerShriekModule_app
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ₀)) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ₀)).obj F ≅
      (lowerShriekModule j Λ₀).obj F where
  hom :=
    liftModuleSheafHom
      ((extensionByZero_compSheafCompose j Λ₀ F).hom ≫
        ((extensionByZeroIsoLowerShriek j).app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})).obj F)).hom ≫
        ((lowerShriekModule_forgetFunctorIso j Λ₀).app F).inv)
  inv :=
    liftModuleSheafHom
      (((lowerShriekModule_forgetFunctorIso j Λ₀).app F).hom ≫
        ((extensionByZeroIsoLowerShriek j).symm.app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})).obj F)).hom ≫
        (extensionByZero_compSheafCompose j Λ₀ F).inv)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level identification of étale extension by zero with finite-support
lower shriek on étale sheaves of `Λ`-modules. -/
def extensionByZeroIsoLowerShriekModule :
    etaleExtensionByZero j (ModuleCat.{u} Λ₀) ≅ lowerShriekModule j Λ₀ :=
  NatIso.ofComponents (extensionByZeroIsoLowerShriekModule_app j Λ₀) sorry

/-- Exact extension by zero and exact finite-support shriek induce the derived
identification. -/
def extensionByZeroDerivedIsoLowerShriekModule
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ₀))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ₀))]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ₀)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ₀)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ₀)]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ₀)).Additive]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ₀))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ₀))] :
    (etaleExtensionByZero j (ModuleCat.{u} Λ₀)).mapDerivedCategory ≅
      lowerShriekModuleDerived j Λ₀ :=
  Functor.MapDerivedCategory.functorIso (extensionByZeroIsoLowerShriekModule j Λ₀)

end ExtensionIso


section CompOn
variable {Y₀ Z₀ : Scheme.{u}} (X₀ : Over Y₀) (g₀ : Y₀ ⟶ Z₀)
variable [IsSeparated X₀.hom] [Scheme.Hom.FiniteType X₀.hom]
variable [IsSeparated g₀] [Scheme.Hom.FiniteType g₀]
variable [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
variable [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
variable [CompactSpace Z₀] [QuasiSeparatedSpace Z₀]
variable (C : CompDiagram X₀ g₀)
variable (Λ₀ : Type u) [CommRing Λ₀]
variable [HasSheafify X₀.left.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasSheafify Y₀.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasSheafify Z₀.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasSheafify (CompDiagram.interior X₀ g₀ C).smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ₀)]
variable [HasDerivedCategory (Sheaf X₀.left.smallEtaleTopology (ModuleCat.{u} Λ₀))]
variable [HasDerivedCategory (Sheaf Y₀.smallEtaleTopology (ModuleCat.{u} Λ₀))]
variable [HasDerivedCategory (Sheaf Z₀.smallEtaleTopology (ModuleCat.{u} Λ₀))]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior X₀ g₀ C).smallEtaleTopology (ModuleCat.{u} Λ₀))]
variable [HasDerivedCategory
  (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ₀))]
variable [HasDerivedCategory
  (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ₀))]
variable [∀ U : X₀.left.Etale,
  HasWeakSheafify (X₀.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ₀)]
variable [∀ U : Y₀.Etale,
  HasWeakSheafify (Y₀.smallEtaleTopology.over U) (ModuleCat.{u} Λ₀)]
variable [∀ U : Z₀.Etale,
  HasWeakSheafify (Z₀.smallEtaleTopology.over U) (ModuleCat.{u} Λ₀)]
variable [∀ U : (CompDiagram.interior X₀ g₀ C).Etale,
  HasWeakSheafify ((CompDiagram.interior X₀ g₀ C).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ₀)]
variable [∀ U : C.P_bar.obj.right.left.Etale,
  HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ₀)]
variable [∀ U : C.P_g.obj.right.left.Etale,
  HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ₀)]
variable [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [Y₀.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [(CompDiagram.interior X₀ g₀ C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [HasSheafCompose C.P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [HasSheafCompose Y₀.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [HasSheafCompose C.P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]
variable [HasSheafCompose (CompDiagram.interior X₀ g₀ C).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ₀) AddCommGrpCat.{u})]

/-- Mid piece of the Lemma 63.8.1 square comparison. -/
def squareMapMid :=
  etaleDerivedLowerShriekPushforward C.P_bar.obj.right.hom
    (CompDiagram.toBase X₀ g₀ C) (CompDiagram.ιBase X₀ g₀ C)
    (CompDiagram.openImmersion X₀ g₀ C) (CompDiagram.square X₀ g₀ C) Λ₀

end CompOn
end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale
end
