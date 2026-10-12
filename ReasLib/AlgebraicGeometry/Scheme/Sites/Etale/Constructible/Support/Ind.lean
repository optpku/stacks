/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Support
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Ind
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [IsNoetherian X]

/-- A locally torsion abelian étale sheaf supported in a specialization-stable subset is a
filtered colimit of constructible sheaves whose supports lie in closed subsets of that subset. -/
theorem isConstructibleEtaleAddCommGrp_ind_of_support
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    {E : Set X} (hE : StableUnderSpecialization E)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (hsupp : abelianSheafSupport F ⊆ E) :
    ObjectProperty.ind.{u + 1}
      (fun G ↦ IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G ∧
        ∃ Z : Set X, IsClosed Z ∧ Z ⊆ E ∧ abelianSheafSupport G ⊆ Z) F := sorry

/-- A sheaf of modules over a Noetherian ring supported in a specialization-stable subset is a
filtered colimit of constructible sheaves whose supports lie in closed subsets of that subset. -/
theorem isConstructibleEtaleModule_ind_of_support
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    {E : Set X} (hE : StableUnderSpecialization E)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hsupp : moduleSheafSupport F ⊆ E) :
    ObjectProperty.ind.{u + 1}
      (fun G ↦ IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G ∧
        ∃ Z : Set X, IsClosed Z ∧ Z ⊆ E ∧ moduleSheafSupport G ⊆ Z) F := sorry

end CategoryTheory.Sheaf
