/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkFunctor

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry

noncomputable section

universe u

namespace GaloisCohomology

/-- The étale sheaf associated to a discrete module for `Gal(Ksep / K)`. -/
def discreteSheaf (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] :
    DiscreteModuleCat ℤ (Gal(Ksep / K)) ⥤
      Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleStalkFunctor K Ksep).asEquivalence.inverse

/-- The stalk of `discreteSheaf` is isomorphic to its input. -/
theorem discreteSheaf_spec (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (M : DiscreteModuleCat ℤ (Gal(Ksep / K))) :
    IsIsomorphic ((etaleStalkFunctor K Ksep).obj ((discreteSheaf K Ksep).obj M)) M := sorry

end GaloisCohomology

end
