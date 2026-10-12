/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison
import StacksCheckRecall

universe u v

/- Lemma 38.34.6 (1): Every fppf covering family is an h covering family. -/
@[stacks 0ETV] #check
  (AlgebraicGeometry.Scheme.FppfCovering.hCovering :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over T},
      AlgebraicGeometry.Scheme.FppfCovering family →
        AlgebraicGeometry.Scheme.HCovering family)

/- Lemma 38.34.6 (2): Every syntomic covering family is an h covering family. -/
@[stacks 0ETV] #check
  (AlgebraicGeometry.Scheme.SyntomicCovering.hCovering :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over T},
      AlgebraicGeometry.Scheme.SyntomicCovering family →
        AlgebraicGeometry.Scheme.HCovering family)

/- Lemma 38.34.6 (3): Every smooth covering family is an h covering family. -/
@[stacks 0ETV] #check
  (AlgebraicGeometry.Scheme.SmoothCovering.hCovering :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over T},
      AlgebraicGeometry.Scheme.SmoothCovering family →
        AlgebraicGeometry.Scheme.HCovering family)

/- Lemma 38.34.6 (4): Every étale covering family is an h covering family. -/
@[stacks 0ETV] #check
  (AlgebraicGeometry.Scheme.hCovering_of_mem_etalePrecoverage :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over T},
      CategoryTheory.Presieve.ofArrows
          (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        AlgebraicGeometry.Scheme.etalePrecoverage.coverings T →
      AlgebraicGeometry.Scheme.HCovering family)

/- Lemma 38.34.6 (5): Every Zariski covering family is an h covering family. -/
@[stacks 0ETV] #check
  (AlgebraicGeometry.Scheme.hCovering_of_mem_zariskiPrecoverage :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over T},
      CategoryTheory.Presieve.ofArrows
          (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        AlgebraicGeometry.Scheme.zariskiPrecoverage.coverings T →
      AlgebraicGeometry.Scheme.HCovering family)
