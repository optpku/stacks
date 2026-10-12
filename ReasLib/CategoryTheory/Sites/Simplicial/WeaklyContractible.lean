/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Hypercovering
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Simplicial.Cech
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Descent along weakly contractible singleton hypercovers

A simplicial object over a site object is a singleton hypercover when its augmentation in
degree zero and all relative matching maps generate covering sieves. Degreewise weak
contractibility identifies its total Čech complex with bounded-below derived sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Plus (Q)

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- A singleton hypercover is a simplicial object over `U` whose degree-zero augmentation
and every relative matching map generate covering sieves. -/
def IsSingletonHypercover (J : GrothendieckTopology C) {U : C}
    (K : SimplicialObject (Over U)) : Prop :=
  MorphismProperty.Hypercovering
    (fun _ _ f ↦ Sieve.generate (Presieve.singleton f) ∈ J _) K

namespace Cech

/-- Derived sections of a bounded-below coefficient complex are computed by the total Čech
complex of a degreewise weakly contractible singleton hypercover. -/
theorem isIsomorphic_rGamma_total (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf J AddCommGrpCat.{w})]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{w}))]
    (K : SimplicialObject (Over U)) (hK : IsSingletonHypercover J K)
    (hW : ∀ n : ℕ, J.IsWeaklyContractible ((K.obj (op (SimplexCategory.mk n))).left))
    (ℰ : CochainComplex.Plus (Sheaf J AddCommGrpCat.{w})) :
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived J U ⋙ DerivedCategory.Plus.ι).obj (Q.obj ℰ))
      (DerivedCategory.Q.obj ((totalFunctor K).obj ℰ.obj)) := sorry

end Cech

end CategoryTheory.SimplicialObject
