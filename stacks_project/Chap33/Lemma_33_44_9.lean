/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.CurveDegree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- The effective Cartier divisor is finite over the base field. -/
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.subschemeIsFinite_of_isProper_of_topologicalKrullDim_le_one :
    ∀ {X : Scheme.{u}} {k : Type u} [Field k]
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι],
      topologicalKrullDim X ≤ 1 → IsFinite (D.subschemeι ≫ f))

/- The divisor degree is the dimension of its ring of global sections. -/
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.curveDegreeOfInvertible_associatedSheaf_eq_finrank_globalSections :
    ∀ {X : Scheme.{u}} {k : Type u} [Field k]
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
      (hdim : topologicalKrullDim X ≤ 1),
      Scheme.Modules.curveDegreeOfInvertible f hdim D.associatedSheaf =
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (D.subschemeι ≫ f)) : ℤ))

/- Lemma 33.44.9: twisting a rank-n locally free sheaf by an effective Cartier divisor adds
n times the divisor degree to its degree. -/
@[stacks 0AYY] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.curveDegree_tensor_associatedSheaf_eq :
    ∀ {X : Scheme.{u}} {k : Type u} [Field k]
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
      (hdim : topologicalKrullDim X ≤ 1)
      (ℰ : X.Modules) (n : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ],
      Scheme.Modules.curveDegree f hdim
          (ℰ ⊗ D.associatedSheaf : X.Modules) n =
        (n : ℤ) * Scheme.Modules.curveDegreeOfInvertible f hdim D.associatedSheaf +
          Scheme.Modules.curveDegree f hdim ℰ n)
