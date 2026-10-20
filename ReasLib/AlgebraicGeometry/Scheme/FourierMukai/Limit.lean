/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- If the base changes of two smooth proper schemes to a directed inverse limit
of quasi-compact, quasi-separated schemes with affine transition morphisms admit
a relative Fourier–Mukai equivalence kernel, then their base changes to some
stage above the distinguished base stage admit such a kernel. -/
theorem FourierMukaiObject.exists_relativeEquivalenceKernel_of_qcqsAffineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}}
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : Scheme.Limit.QcqsAffineLimit D)
    (X0 Y0 : FourierMukaiObject (D.obj (OrderDual.toDual s.base)))
    (K : RingedSpace.ModuleDerived.Perfect (X :=
      (Limits.pullback
        (FourierMukaiObject.baseChange
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) X0).hom
        (FourierMukaiObject.baseChange
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) Y0).hom).toRingedSpace))
    [IsIso (C := FourierMukaiObject s.limitCone.cone.pt)
      (Quotient.mk'' K :
        FourierMukaiObject.baseChange
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) X0 ⟶
        FourierMukaiObject.baseChange
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) Y0)] :
    ∃ (i : I) (h : s.base ≤ i)
        (Ki : RingedSpace.ModuleDerived.Perfect (X :=
          (Limits.pullback
            (FourierMukaiObject.baseChange (D.map (homOfLE h)) X0).hom
            (FourierMukaiObject.baseChange (D.map (homOfLE h)) Y0).hom).toRingedSpace)),
      IsIso (C := FourierMukaiObject (D.obj (OrderDual.toDual i)))
        (Quotient.mk'' Ki :
          FourierMukaiObject.baseChange (D.map (homOfLE h)) X0 ⟶
          FourierMukaiObject.baseChange (D.map (homOfLE h)) Y0) :=
  sorry
