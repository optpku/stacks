/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_2_1_Opens
public import stacks_project.Chap85.Lemma_85_2_1_Site

/-!
# Component inclusion of a simplicial space

The degree-`n` inclusion `DiagramOpens.fiber X (op ⦋n⦌)`, `U ↦ U`, and the associated
morphism of topoi `g_n : Sh(X_n) ⟶ Sh(X_Zar)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

universe u

namespace CategoryTheory.SimplicialObject

/-- The degree-`n` inclusion `X_{n,Zar} ⥤ X_Zar` sending an open `U ⊂ X_n` to the same
open in `DiagramOpens X`. -/
abbrev component (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    Opens (X.obj (op ⦋n⦌)) ⥤ DiagramOpens X :=
  DiagramOpens.fiber X (op ⦋n⦌)

/-- The component functor sends an open of `X.obj (op ⦋n⦌)` to `DiagramOpens.ofOpens`. -/
theorem component_obj (X : SimplicialObject TopCat.{u}) (n : ℕ)
    (U : Opens (X.obj (op ⦋n⦌))) :
    (component X n).obj U = DiagramOpens.ofOpens X (op ⦋n⦌) U := sorry

/-- The component inclusion preserves pullbacks of opens. -/
instance instComponentPreservesLimitsOfShapeWalkingCospan
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan (component X n) := sorry

/-- The component inclusion preserves equalizers of opens. -/
instance instComponentPreservesLimitsOfShapeWalkingParallelPair
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    PreservesLimitsOfShape WalkingParallelPair (component X n) := sorry

/-- The morphism of topoi `g_n : Sh(X_n) ⟶ Sh(X_Zar)` associated to the component inclusion. -/
noncomputable def componentMorphism (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F] :
    MorphismOfTopoiIn (zariskiTopology X)
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) :=
  (component X n).morphismOfTopoiInOfCocontinuous
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Restriction of sheaves along the component inclusion, i.e. `F ↦ F_n`. -/
abbrev sheafComponent (X : SimplicialObject TopCat.{u}) (n : ℕ)
    (A : Type (u + 1)) [Category.{u} A]
    [(component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)] :
    Sheaf (zariskiTopology X) A ⥤
      Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) A :=
  (component X n).sheafPushforwardContinuous A
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Type-valued lower shriek `g^{Sh}_{n!}` along the component inclusion. -/
noncomputable abbrev sheafLowerShriek (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasLeftKanExtension P] :
    Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u) ⥤
      Sheaf (zariskiTopology X) (Type u) :=
  (component X n).sheafPullback (Type u)
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Abelian lower shriek `g_{n!}` along the component inclusion. -/
noncomputable abbrev abelianLowerShriek (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasWeakSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasLeftKanExtension P] :
    Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u} ⥤
      Sheaf (zariskiTopology X) AddCommGrpCat.{u} :=
  (component X n).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Inverse image of `g_n` is the sheafified cocontinuous pullback along the component
inclusion. -/
theorem componentMorphism_inverseImage (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F] :
    (componentMorphism X n)⁻¹ =
      (component X n).sheafPullbackCocontinuous (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) := sorry

/-- The canonical cocontinuous-to-continuous comparison along the component inclusion. -/
noncomputable def inverseImageIso (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [(component X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasWeakSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F] :
    (component X n).sheafPullbackCocontinuous (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) ≅
      sheafComponent X n (Type u) :=
  asIso (Functor.CocontinuousPullback.comparison.{u} (component X n)
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X))

/-- Type-valued lower shriek is left adjoint to restriction along the component inclusion. -/
noncomputable def sheafLowerShriek_adjunction (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasLeftKanExtension P] :
    sheafLowerShriek X n ⊣ sheafComponent X n (Type u) :=
  (component X n).sheafAdjunctionContinuous (Type u)
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Abelian lower shriek is left adjoint to restriction along the component inclusion. -/
noncomputable def abelianLowerShriek_adjunction (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasWeakSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasLeftKanExtension P] :
    abelianLowerShriek X n ⊣ sheafComponent X n AddCommGrpCat.{u} :=
  (component X n).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

end CategoryTheory.SimplicialObject
