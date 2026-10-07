module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Affine
import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.AffinePlane
import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Comparison
import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.StalkSpectrum
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Example 59.15.3 (1): every Zariski open covering of a scheme is an fpqc
covering family. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.OpenCover.fpqcCovering :
    ∀ {T : Scheme.{u}} (cover : Scheme.OpenCover T),
      Scheme.FpqcCovering
        (fun i : cover.I₀ ↦ CategoryTheory.Over.mk (cover.f i)))

/- Example 59.15.3 (2): a singleton affine spectrum family is fpqc exactly
when the corresponding ring map is faithfully flat. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.covering_spec_iff_faithfullyFlat :
    ∀ {A B : CommRingCat.{u}} (f : A ⟶ B),
      Scheme.FpqcCovering
        (fun _ : PUnit ↦ CategoryTheory.Over.mk (Spec.map f)) ↔
        f.hom.FaithfullyFlat)

/- Example 59.15.3 (3): a flat, surjective, quasi-compact morphism gives a
singleton fpqc covering family. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.covering_singleton_of_flat_surjective_quasiCompact :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f],
      Scheme.FpqcCovering (fun _ : Unit ↦ CategoryTheory.Over.mk f))

/- Example 59.15.3 (4): the stalk-spectrum coproduct morphism for affine
one-space over a field is flat. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.AffineLineStalkSpectrum.flat :
    ∀ (k : Type u) [Field k],
      Flat (AlgebraicGeometry.stalkSpectrumCoproductTo
        (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k)))

/- Example 59.15.3 (5): the stalk-spectrum coproduct morphism for affine
one-space over a field is surjective. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.AffineLineStalkSpectrum.surjective :
    ∀ (k : Type u) [Field k],
      Surjective (AlgebraicGeometry.stalkSpectrumCoproductTo
        (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k)))

/- Example 59.15.3 (6): this stalk-spectrum coproduct morphism is not
quasi-compact. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.AffineLineStalkSpectrum.not_quasiCompact :
    ∀ (k : Type u) [Field k],
      ¬ QuasiCompact (AlgebraicGeometry.stalkSpectrumCoproductTo
        (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k)))

/- Example 59.15.3 (7): its singleton family is not fpqc despite flatness and
surjectivity. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.AffineLineStalkSpectrum.not_covering :
    ∀ (k : Type u) [Field k],
      ¬ Scheme.FpqcCovering
        (fun _ : PUnit ↦ CategoryTheory.Over.mk
          (AlgebraicGeometry.stalkSpectrumCoproductTo
            (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k))))

/- Example 59.15.3 (8): adjoining the formal power-series spectrum to the two
standard affine-plane opens gives an fpqc covering family. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.AffinePlaneFamily.powerSeries_fpqcCovering :
    ∀ (k : Type u) [Field k],
      Scheme.FpqcCovering (AlgebraicGeometry.Scheme.Fpqc.AffinePlaneFamily.powerSeries k))

/- Example 59.15.3 (9): adjoining the origin stalk spectrum to the two
standard affine-plane opens gives an fpqc covering family. -/
@[stacks 03NY] #check
  (AlgebraicGeometry.Scheme.Fpqc.AffinePlaneFamily.stalk_fpqcCovering :
    ∀ (k : Type u) [Field k],
      Scheme.FpqcCovering (AlgebraicGeometry.Scheme.Fpqc.AffinePlaneFamily.stalk k))
