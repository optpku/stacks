module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import Mathlib.CategoryTheory.EssentialImage

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Over an adically complete Noetherian ring admitting a dualizing complex, a
coherent formal module satisfying the strict `(1, 1 + d)` inequalities and already
in the essential image of completion admits a coherent algebraization with stalk
depth at least two wherever the point closure meets the closed fiber only inside
the excluded closed subset, provided the ideal has local cohomological dimension
at most `d` and `d ≥ 1`. This algebraization is unique up to a unique isomorphism
compatible with its completion presentation. -/
@[stacks 0EJ8]
theorem existsUniqueAlgebraizationWithDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
    [IsAdicComplete S.I A]
    (d : ℤ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_isCompletion :
      (CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)
    (h_strict : SatisfiesStrictInequalities S F 1 (1 + d)) :
    ∃ G : RingedSpace.Coh (S.U.toScheme).toRingedSpace,
      ∃ e : (CoherentCompletion.functor
          ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).obj G ≅ F,
        (∀ x : S.U,
          closure ({S.U.ι x} : Set S.X) ∩ Set.range S.y ⊆ Set.range S.z →
            (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
              (RingedSpace.stalkModuleCat G.obj x)) ∧
        ∀ (G' : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
            (e' : (CoherentCompletion.functor
              ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).obj G' ≅ F),
          (∀ x : S.U,
            closure ({S.U.ι x} : Set S.X) ∩ Set.range S.y ⊆ Set.range S.z →
              (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
                (RingedSpace.stalkModuleCat G'.obj x)) →
            ∃! i : G ≅ G',
              (CoherentCompletion.functor
                ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).mapIso i ≪≫ e' = e := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
