/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Sites.Proetale.Hypercovering
import StacksCheckRecall

/-!
# Lemma 61.14.2

On the small pro-étale site, derived sections of a bounded-below complex of abelian sheaves
over a weakly contractible singleton hypercovering are the total complex of the hypercovering
Čech bicomplex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open DerivedCategory.Plus (Q)

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.14.2: derived sections of a bounded-below representative over an arbitrary
small pro-étale object are computed by the total Čech complex of a degreewise weakly
contractible singleton hypercover. -/
@[stacks 09A2] #check (AlgebraicGeometry.Scheme.ProEt.rGamma_isIsomorphic_totalCech :
  ∀ {X : Scheme.{u}}
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})] (U : X.ProEt)
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) U).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]
    (K : SimplicialObject (Over U))
    (hK : SimplicialObject.IsSingletonHypercover (topology X) K)
    (hW : ∀ n : ℕ,
      (topology X).IsWeaklyContractible ((K.obj (op (SimplexCategory.mk n))).left))
    (ℰ : CochainComplex.Plus (Sheaf (topology X) AddCommGrpCat.{u})),
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived (topology X) U ⋙
        DerivedCategory.Plus.ι).obj (Q.obj ℰ))
      (DerivedCategory.Q.obj ((SimplicialObject.Cech.totalFunctor K).obj ℰ.obj)))

end AlgebraicGeometry.Scheme.ProEt

end
