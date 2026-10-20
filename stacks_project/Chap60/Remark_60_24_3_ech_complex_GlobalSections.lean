module

public import stacks_project.Chap60.Lemma_60_18_2
public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

namespace CrystallineModuleSheaf

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (F : CrisModuleSheaf S I γ h_compatible X x₀)

/-- The underlying abelian sheaf with coefficients in the universe of the crystalline site. -/
def abelianSheaf :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    AddCommGrpCat.{u + 1}).obj
      (toAbelianPresheaf S I γ h_compatible X x₀ F ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u})

/-- The coefficient sheaf is the sheafification of the universe-raised section presheaf. -/
theorem abelianSheaf_obj :
    abelianSheaf p S I γ h_compatible s X x₀ h_p F =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        AddCommGrpCat.{u + 1}).obj
          (toAbelianPresheaf S I γ h_compatible X x₀ F ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u}) := sorry

/-- Crystalline derived global sections, using the right adjoint of the constant sheaf functor. -/
def derivedGlobalSections : DerivedCategory AddCommGrpCat.{u + 1} :=
  (Functor.RightDerived.Cochain.functor
    (Sheaf.Γ (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.singleFunctor
          (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
            AddCommGrpCat.{u + 1}) 0).obj
              (abelianSheaf p S I γ h_compatible s X x₀ h_p F))

/-- Derived global sections apply the total right derived global-sections functor in degree zero. -/
theorem derivedGlobalSections_def :
    derivedGlobalSections p S I γ h_compatible s X x₀ h_p F =
      (Functor.RightDerived.Cochain.functor
        (Sheaf.Γ (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u + 1})).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
                AddCommGrpCat.{u + 1}) 0).obj
                  (abelianSheaf p S I γ h_compatible s X x₀ h_p F)) := sorry

end CrystallineModuleSheaf
