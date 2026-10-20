module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HyperplaneSection.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Remark 33.35.5: for every integral twist, a short exact hyperplane-section sequence
`0 ⟶ ℱ(d - 1) ⟶ ℱ(d) ⟶ i_*i^*ℱ(d) ⟶ 0` induces an exact cohomology sequence; when the
hyperplane is identified with `ℙ^(n - 1)_k`, the pushforward terms are the cohomology of the
corresponding restricted twists on that projective space. -/
@[stacks 0EGK] #check
  (AlgebraicGeometry.hyperplaneSectionTwistedShortExactFor_of_hyperplaneSectionShortExact :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
      (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections),
      AlgebraicGeometry.hyperplaneSectionShortExactFor P ℱ s →
        ∀ d : ℤ,
          (AlgebraicGeometry.hyperplaneSectionTwistedShortComplex P ℱ s d).ShortExact)

#check
  (AlgebraicGeometry.exists_iso_projectiveSpace_pred_pullback_tautologicalSheaf_of_hyperplane :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n) (hn : 1 ≤ n)
      {H : Scheme.{u}} (i : H ⟶ P.scheme)
      (hHyperplane : ProjectiveSpaceHyperplane P i),
      ∃ (P' : ProjectiveSpaceOver (Spec (CommRingCat.of k)) (n - 1)) (φ : P'.scheme ≅ H)
        (e :
          (Scheme.Modules.pullback φ.hom).obj
              ((Scheme.Modules.pullback i).obj P.tautologicalSheaf) ≅
            P'.tautologicalSheaf),
        φ.hom ≫ i ≫ P.hom = P'.hom)

#check
  (AlgebraicGeometry.hyperplaneSectionTwistedCohomologySequence_exact :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
      (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ)
      (hℱ : AlgebraicGeometry.hyperplaneSectionShortExactFor P ℱ s) (q : ℕ),
      (AlgebraicGeometry.hyperplaneSectionTwistedCohomologyWindow P ℱ s d
        (AlgebraicGeometry.hyperplaneSectionTwistedShortExactFor_of_hyperplaneSectionShortExact
          P ℱ s hℱ d) q).Exact)

#check
  (AlgebraicGeometry.hyperplaneSectionTwistedRestrictionPushforwardCohomology_isomorphic :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
      (ℱ : P.scheme.Modules) [ℱ.IsQuasicoherent]
      (s : P.tautologicalSheaf.sections)
      [ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s)] (d : ℤ) (q : ℕ),
      IsIsomorphic
        ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing P.scheme.toRingedSpace))
          AddCommGrpCat.{u}).obj
            ((((RingedSpace.Module.Derived.GlobalSections.Delta.cohomology
              P.scheme.toRingedSpace).F q).obj).obj
                (AlgebraicGeometry.hyperplaneSectionTwistedRestrictionPushforward P ℱ s d)))
        (AlgebraicGeometry.hyperplaneSectionTwistedHyperplaneCohomology P ℱ s d q))
