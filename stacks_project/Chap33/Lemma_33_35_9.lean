module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.HyperplaneSection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

/- Lemma 33.35.9: in the hyperplane-section setup, if a coherent module sheaf on standard
projective `n`-space is `m`-regular, then its transported restriction is `m`-regular on standard
projective `(n - 1)`-space. -/
@[stacks 08A5] #check
  (AlgebraicGeometry.ProjectiveSpace.IsMRegular.hyperplaneRestriction_of_nonzero :
    ∀ {k : Type u} [Field k] [Infinite k] {n : ℕ} (hn : 1 ≤ n) {m : ℤ}
      (ℱ : (ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent]
      (𝒢 : (ProjectiveSpace.scheme k (n - 1)).Modules) [𝒢.IsCoherent]
      (Q : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
      (eQ : Q.scheme ≅ ProjectiveSpace.scheme k n) (s : Q.tautologicalSheaf.sections)
      (hs : Q.tautologicalSheaf.unitHomEquiv.symm s ≠ 0)
      (φ : ProjectiveSpace.scheme k (n - 1) ≅ Q.tautologicalZeroScheme s)
      (h𝒢 : 𝒢 ≅ ProjectiveSpace.transportedHyperplaneRestriction Q eQ s φ ℱ)
      (hShortExact :
        hyperplaneSectionShortExactFor Q ((Scheme.Modules.pullback eQ.hom).obj ℱ) s)
      (hAmbientTwistIso : ∀ d : ℤ,
        (Scheme.Modules.pullback eQ.hom).obj (ProjectiveSpace.twistingSheaf k n d) ≅
          @Scheme.Modules.tensorPowerInt Q.scheme Q.tautologicalSheaf
            Q.tautologicalSheaf_isInvertible d)
      (hRestrictionTwistIso : ∀ d : ℤ,
        (Scheme.Modules.pullback
            (ProjectiveSpace.transportedHyperplaneInclusion Q eQ s φ)).obj
            (ProjectiveSpace.twistingSheaf k n d) ≅
          ProjectiveSpace.twistingSheaf k (n - 1) d)
      (hℱ : ProjectiveSpace.IsMRegular k n ℱ m),
      ProjectiveSpace.IsMRegular k (n - 1) 𝒢 m)
