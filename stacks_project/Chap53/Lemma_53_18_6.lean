/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PicardTorsion.Bound
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.18.6: for a proper scheme `X` of dimension at most one over a field `k`,
the `ZMod ℓ`-dimension of the prime-to-characteristic `ℓ`-torsion in `Pic(X)` is at most
`dim_k H¹(X, 𝒪_X) + g_geom(X / k)`. -/
@[stacks 0CE6] #check
  (AlgebraicGeometry.SchemeOverField.picardTorsionFinrank_le :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
      (h_prime_to_char : DVR.Field.PrimeToChar k ℓ),
      @Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ)) _ _
          (AddSubgroup.torsionBy.zmodModule :
            Module (ZMod ℓ) (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ))) ≤
        Scheme.Hom.cohomologyFinrank X.hom
            (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 +
          GeometricGenus.ofScheme X hdim)

end AlgebraicGeometry.SchemeOverField
