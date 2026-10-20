/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Component
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u}) (n : ℕ)

/- Lemma 85.2.5 (1): the functor `X_{n,Zar} ⥤ X_Zar`, `U ↦ U`, is continuous. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.component_isContinuous X n :
  (component X n).IsContinuous
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X))

/- Lemma 85.2.5 (2): the functor `X_{n,Zar} ⥤ X_Zar`, `U ↦ U`, is cocontinuous. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.component_isCocontinuous X n :
  (component X n).IsCocontinuous
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X))

/- Lemma 85.2.5 (3): `g_n⁻¹` associates to a sheaf `F` on `X_Zar` the sheaf `F_n` on
`X_n`. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.componentMorphism_inverseImage_iso_sheafComponent X n :
  (componentMorphism X n)⁻¹ ≅ sheafComponent X n (Type u))

/- Lemma 85.2.5 (4): `g_n⁻¹ : Sh(X_Zar) ⥤ Sh(X_n)` has a left adjoint
`g^{Sh}_{n!}`. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.sheafLowerShriek_adjunction X n :
  sheafLowerShriek X n ⊣ sheafComponent X n (Type u))

/- Lemma 85.2.5 (5): `g^{Sh}_{n!}` commutes with finite connected limits. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.sheafLowerShriek_preservesFiniteConnectedLimits X n :
  PreservesFiniteConnectedLimits (sheafLowerShriek X n))

/- Lemma 85.2.5 (6): `g_n⁻¹ : Ab(X_Zar) ⥤ Ab(X_n)` has a left adjoint `g_{n!}`. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.abelianLowerShriek_adjunction X n :
  abelianLowerShriek X n ⊣ sheafComponent X n AddCommGrpCat.{u})

/- Lemma 85.2.5 (7): `g_{n!}` is exact. -/
@[stacks 09W0] #check (CategoryTheory.SimplicialObject.abelianLowerShriek_exact X n :
  exactFunctor
    (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u})
    (Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (abelianLowerShriek X n))

end CategoryTheory.SimplicialObject
