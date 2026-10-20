/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Depth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.19.7: a coherent formal module satisfying the strict `(1, 1 + d)`
inequalities and already known to be a completion has a unique coherent
algebraization with the required stalk-depth condition. -/
@[stacks 0EJ8] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.existsUniqueAlgebraizationWithDepth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
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
    (h_strict : SatisfiesStrictInequalities S F 1 (1 + d)),
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
                ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).mapIso i ≪≫ e' = e)

end AlgebraicGeometry.Scheme.CoherentFormalModules
