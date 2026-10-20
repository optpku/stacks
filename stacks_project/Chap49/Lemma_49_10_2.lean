/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Invertible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry Algebra.DualModule

universe u

/- Lemma 49.10.2 (1): for a quasi-finite flat homomorphism of Noetherian rings,
the relative dualizing module is invertible if and only if the relative dualizing module
of every residue-field fibre is invertible. -/
@[stacks 0DWK] #check
  (Algebra.RelativeDualizingModule.Presentation.invertible_iff_fiberwise :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
      (h_quasiFinite : RingHom.FiniteType.QuasiFinite (algebraMap A B))
      (P : Algebra.RelativeDualizingModule.Presentation
        (CommRingCat.ofHom (algebraMap A B))),
      Module.Invertible B (P.module inferInstance inferInstance h_quasiFinite) ↔
        ∀ p : PrimeSpectrum A,
          Module.Invertible (p.asIdeal.Fiber B)
            (Algebra.DualModule.of p.asIdeal.ResidueField (p.asIdeal.Fiber B)))

/- Lemma 49.10.2 (2): for a quasi-finite flat morphism of Noetherian schemes,
the relative dualizing sheaf is invertible if and only if its pullback to every fibre is
invertible. -/
@[stacks 0DWK] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.invertible_iff_fiberwise :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf),
      Scheme.Modules.Invertible W.module.obj ↔
        ∀ x : X,
          Scheme.Modules.Invertible
            ((Scheme.Modules.pullback (f.fiberι x)).obj W.module.obj))
