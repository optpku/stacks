/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalInequalities
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.20.4 (1): a coherent formal module satisfying the principal `(2, 3)`-inequalities extends to the ambient affine scheme under the local dualizing hypotheses. -/
@[stacks 0EJ9] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.extendsTo_of_principal_inequalities :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (f : A)
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_ineq : SatisfiesInequalities S F 2 3),
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F)

/- Lemma 52.20.4 (2): under adic completeness, the same coherent formal module is the canonical coherent completion of a coherent module on the open complement. -/
@[stacks 0EJ9] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_principal_inequalities :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (f : A)
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_ineq : SatisfiesInequalities S F 2 3),
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
