/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine
public import stacks_project.Chap57.Lemma_57_15_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Lemma 57.15.4: if `S` is a directed inverse limit of qcqs schemes with affine
transition morphisms, `X0` and `Y0` are smooth proper over a distinguished stage
`S0`, and `K` is the Fourier--Mukai kernel of a relative equivalence from the
base-changed pair over `S`, then some later stage `Si` admits a Fourier--Mukai
kernel of a relative equivalence from `Xi` to `Yi` over `Si`. -/
@[stacks 0G0L]
theorem FourierMukaiObject.exists_relativeEquivalenceKernel_of_qcqsAffineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}}
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : Scheme.Limit.QcqsAffineLimit D)
    (X0 Y0 : FourierMukaiObject (D.obj (OrderDual.toDual s.base)))
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback
        (FourierMukaiObject.baseChange
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) X0).hom
        (FourierMukaiObject.baseChange
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) Y0).hom).toRingedSpace)
    [FourierMukaiObject.IsRelativeEquivalenceKernel K] :
    ∃ (i : I) (h : s.base ≤ i)
        (Ki : @RingedSpace.ModuleDerived.Perfect
          (Limits.pullback
            (FourierMukaiObject.baseChange (D.map (homOfLE h)) X0).hom
            (FourierMukaiObject.baseChange (D.map (homOfLE h)) Y0).hom).toRingedSpace),
      FourierMukaiObject.IsRelativeEquivalenceKernel Ki :=
  sorry
