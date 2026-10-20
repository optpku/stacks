/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.FiniteSectionImages
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.16.10 (1): write `M = sectionsLimit S F`. If the global-section
system of a coherent formal module on `S.U` is Mittag-Leffler, the limit topology
on `M` is its `S.I`-adic topology, and the image of every canonical projection
`M ⟶ H⁰(S.U, Fₙ)` is a finite `A`-module, then `F` canonically extends to `S.X`. -/
@[stacks 0EHH] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_finiteSectionImages :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_mittagLeffler : IsMittagLeffler (sectionsSystem S F))
      (h_topology : Functor.limitTopology (sectionsSystem S F) =
        Ideal.adicModuleTopology S.I (sectionsLimit S F))
      (h_finite : ∀ n : ℕ,
        Module.Finite A (LinearMap.range (limit.π (sectionsSystem S F) (op n)).hom)),
      CanonicallyExtends S F)

/- Lemma 52.16.10 (2): under the same hypotheses, if `A` is `S.I`-adically
complete, then `F` lies in the essential image of completion from coherent
`𝒪_{S.U}`-modules. -/
@[stacks 0EHH] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_finiteSectionImages :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_mittagLeffler : IsMittagLeffler (sectionsSystem S F))
      (h_topology : Functor.limitTopology (sectionsSystem S F) =
        Ideal.adicModuleTopology S.I (sectionsLimit S F))
      (h_finite : ∀ n : ℕ,
        Module.Finite A (LinearMap.range (limit.π (sectionsSystem S F) (op n)).hom)),
      (CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
