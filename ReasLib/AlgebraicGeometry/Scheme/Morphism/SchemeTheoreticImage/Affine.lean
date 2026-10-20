/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme-theoretic images of affine spectrum maps

This file identifies the kernel ideal sheaf of a map of affine spectra and uses that
identification to present its scheme-theoretic image as the spectrum of the quotient by the
ring-map kernel.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The kernel ideal sheaf of `Spec.map phi` is induced by the kernel of `phi` on global
sections. -/
@[stacks 056A "kernel ideal sheaf of an affine spectrum map"]
theorem ker_specMap {A B : CommRingCat.{u}} (phi : A ⟶ B) :
    (Spec.map phi).ker = Scheme.IdealSheafData.ofIdealTop
      ((RingHom.ker phi.hom).map (Scheme.ΓSpecIso A).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  calc
    RingHom.ker (Spec.map phi).appTop.hom =
        RingHom.ker ((Scheme.ΓSpecIso B).hom.hom.comp (Spec.map phi).appTop.hom) :=
      (RingHom.ker_equiv_comp _
        (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv).symm
    _ = RingHom.ker (phi.hom.comp (Scheme.ΓSpecIso A).hom.hom) := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        Scheme.ΓSpecIso_naturality]
    _ = (RingHom.ker phi.hom).comap (Scheme.ΓSpecIso A).hom.hom :=
      (RingHom.comap_ker _ _).symm
    _ = (RingHom.ker phi.hom).map (Scheme.ΓSpecIso A).inv.hom := by
      exact Ideal.comap_symm
        (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- If a ring map has kernel `I`, the scheme-theoretic image of its map on spectra is
canonically isomorphic over `Spec A` to `Spec (A / I)`. -/
@[stacks 056A]
theorem schemeTheoreticImage_specMap_iso_quotientOfKernel
    {A B : CommRingCat.{u}} (phi : A ⟶ B) (I : Ideal A)
    (hI : RingHom.ker phi.hom = I) :
    ∃ e : Scheme.Hom.image (Spec.map phi) ≅ Spec (CommRingCat.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Scheme.Hom.imageι (Spec.map phi) := by
  let q : Spec (CommRingCat.of (A ⧸ I)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hker : (Spec.map phi).ker = q.ker := by
    dsimp only [q]
    rw [Scheme.Hom.ker_specMap, Scheme.Hom.ker_specMap, hI]
    change Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso A).inv.hom) =
      Scheme.IdealSheafData.ofIdealTop
        ((RingHom.ker (Ideal.Quotient.mk I)).map (Scheme.ΓSpecIso A).inv.hom)
    rw [Ideal.mk_ker]
  change ∃ e : (Spec.map phi).ker.subscheme ≅ Spec (CommRingCat.of (A ⧸ I)),
    e.hom ≫ q = (Spec.map phi).ker.subschemeι
  rw [hker]
  refine ⟨(asIso q.toImage).symm, ?_⟩
  rw [← cancel_epi (asIso q.toImage).hom]
  simp

end AlgebraicGeometry
