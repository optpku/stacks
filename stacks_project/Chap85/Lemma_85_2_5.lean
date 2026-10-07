module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_2_1_Opens
public import stacks_project.Chap85.Lemma_85_2_1_Site
public import stacks_project.Chap85.Lemma_85_2_5_Component

/-!
# Lemma 85.2.5

The degree-`n` inclusion of the Zariski site of a simplicial space is continuous and
cocontinuous. The associated morphism of topoi `g_n : Sh(X_n) ⟶ Sh(X_Zar)` has inverse
image given by restriction `F ↦ F_n`, that inverse image admits a left adjoint
`g^{Sh}_{n!}` preserving finite connected limits, and on abelian sheaves the corresponding
`g_{n!}` exists and is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/-- Lemma 85.2.5 (1): the functor `X_{n,Zar} ⥤ X_Zar`, `U ↦ U`, is continuous. -/
@[stacks 09W0, instance]
instance component_isContinuous (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) :=
  sorry

/-- Lemma 85.2.5 (2): the functor `X_{n,Zar} ⥤ X_Zar`, `U ↦ U`, is cocontinuous. -/
@[stacks 09W0, instance]
instance component_isCocontinuous (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (component X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) :=
  sorry

/-- Lemma 85.2.5 (3): `g_n⁻¹` associates to a sheaf `F` on `X_Zar` the sheaf `F_n` on `X_n`. -/
@[stacks 09W0]
def componentMorphism_inverseImage_iso_sheafComponent
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F] :
    (componentMorphism X n)⁻¹ ≅ sheafComponent X n (Type u) :=
  CategoryTheory.eqToIso
      (Functor.morphismOfTopoiInOfCocontinuous_inverseImage (component X n)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)) ≪≫
    inverseImageIso X n

/-- Lemma 85.2.5 (4): `g_n⁻¹ : Sh(X_Zar) ⥤ Sh(X_n)` has a left adjoint `g^{Sh}_{n!}`. -/
@[stacks 09W0, instance]
instance sheafComponent_isRightAdjoint (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasLeftKanExtension P] :
    (sheafComponent X n (Type u)).IsRightAdjoint :=
  (sheafLowerShriek_adjunction X n).isRightAdjoint

/-- Lemma 85.2.5 (5): `g^{Sh}_{n!}` commutes with finite connected limits. -/
@[stacks 09W0, instance]
instance sheafLowerShriek_preservesFiniteConnectedLimits
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseLeftKanExtension P] :
    PreservesFiniteConnectedLimits (sheafLowerShriek X n) := sorry

/-- Lemma 85.2.5 (6): `g_n⁻¹ : Ab(X_Zar) ⥤ Ab(X_n)` has a left adjoint `g_{n!}`. -/
@[stacks 09W0, instance]
instance abelianSheafComponent_isRightAdjoint (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasLeftKanExtension P] :
    (sheafComponent X n AddCommGrpCat.{u}).IsRightAdjoint :=
  (abelianLowerShriek_adjunction X n).isRightAdjoint

/-- Lemma 85.2.5 (7): `g_{n!}` is exact. -/
@[stacks 09W0]
theorem abelianLowerShriek_exact (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasPointwiseLeftKanExtension P] :
    exactFunctor
      (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u})
      (Sheaf (zariskiTopology X) AddCommGrpCat.{u})
      (abelianLowerShriek X n) := sorry

end CategoryTheory.SimplicialObject
