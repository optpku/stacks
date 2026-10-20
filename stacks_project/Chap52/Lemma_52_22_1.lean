/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.CohomologicalDimensionOne
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.22.1 -/
@[stacks 0EJI] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_proDepth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (h_dualizing :
        ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
      (h_cd :
        Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
      (F : CoherentFormalModules S.U.toScheme
        ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_pro : (∃ G : SequentialInverseSystem
            (RingedSpace.Coh ((S.U.toScheme).toRingedSpace)),
          (Nonempty
              ((Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj F.obj ≅
                (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj G) ∧
            (∀ (n : ℕ) (y : S.Y) (hy : S.y y ∈ S.U),
              (3 : ℕ∞) ≤
                moduleDepth ((S.U.toScheme).presheaf.stalk
                  (closedFiberOpenPoint S y hy))
                  (RingedSpace.stalkModuleCat
                    ((G.obj (op n)).obj)
                    (closedFiberOpenPoint S y hy)) +
                  algebraizationDistance S y)))),
      CanonicallyExtends S F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
