/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Blowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.30.3: for an affine, finitely presented, flat morphism with geometrically integral
fibres over a quasi-compact quasi-separated base, a finite-type quasicoherent module that is
finitely presented over a quasi-compact open and flat at the generic points of fibres over that
open admits an admissible blowup whose strict transform is finite locally free on a surjective
open. -/
@[stacks 0811] #check
  (AlgebraicGeometry.Scheme.Modules.exists_isAdmissibleBlowup_finiteLocallyFreeOpen :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) [IsAffineHom f] [Scheme.Hom.FinitePresentation f]
      [Flat f] [GeometricallyIntegral f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (U : S.Opens) [QuasiCompact U.ι]
      [(ℱ.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation],
      flatOverInCodimensionZero
          (ℱ.restrict ((f ⁻¹ᵁ U).ι)) (f ∣_ U) →
        ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
          IsAdmissibleBlowupCenter U b I ∧
            ∃ V : (strictTransformAmbient b f).Opens,
              ((strictTransformModule b (I.comap b) f ℱ).restrict V.ι).IsFiniteLocallyFree ∧
                Surjective (V.ι ≫ pullback.snd f b))

end AlgebraicGeometry.Scheme.Modules
