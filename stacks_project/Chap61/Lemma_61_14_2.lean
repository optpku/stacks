module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import stacks_project.Chap61.Lemma_61_14_2_Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.14.2

On the small pro-étale site, derived sections of a bounded-below complex of abelian sheaves
over a weakly contractible singleton hypercovering are the total complex of the hypercovering
Čech bicomplex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Hypercovering
open CategoryTheory.Hypercovering.Cech
open DerivedCategory.Plus (Q)

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Lemma 61.14.2: if `E ∈ D⁺(X.ProEt)` is represented by a bounded-below complex `ℰ` of
abelian sheaves and `K` is a hypercovering of `U` with each `K.family n` a singleton weakly
contractible object, then `RΓ(U, E)` is isomorphic to `Tot(s(ℰ(K)))` in `D(Ab)`. -/
@[stacks 09A2]
theorem rGamma_isIsomorphic_totalCech {X : Scheme.{u}}
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})] (U : X.ProEt)
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) U).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]
    (K : Hypercovering.{u} (topology X) U) (hK : IsWeaklyContractibleSingleton K)
    (ℰ : CochainComplex.Plus (Sheaf (topology X) AddCommGrpCat.{u})) :
    IsIsomorphic
      ((derivedSectionsUlift (topology X) U).obj (Q.obj ℰ))
      (DerivedCategory.Q.obj ((totalFunctor K).obj ℰ.obj)) := sorry

end AlgebraicGeometry.Scheme.ProEt

end
