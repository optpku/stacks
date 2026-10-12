/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenRestriction
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction

/-!
# Restriction of kernel ideal sheaves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom.KernelIdealRestriction

/-- The pullback of the kernel-ideal inclusion along an ambient open immersion, regarded as a
map to the structure sheaf of the restricted target. -/
@[stacks 01IN "restriction pullback of the kernel-ideal inclusion"]
noncomputable abbrev toStructureSheaf
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X) :
    (RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding).toShHom).obj
        (kernelIdealSheaf i) ⟶
      SheafOfModules.unit
        (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding).toRingedSpace) :=
  (kernelIdealSubobject i).pullbackMap (X.ofRestrict U.isOpenEmbedding)

/-- The pulled-back kernel-ideal inclusion factors through the kernel ideal of the restricted
morphism. -/
@[stacks 01IN "restriction kernel-ideal factorization"]
theorem toStructureSheaf_factors
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X)
    {iU : Z.restrict (i.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding}
    (hiU : i.IsOpenRestriction (i.preimageOpen U) U iU) :
    (kernelIdealSubobject iU).Factors
      (toStructureSheaf i U) := sorry

/-- The pulled-back kernel-ideal inclusion is a monomorphism. -/
@[stacks 01IN "restriction kernel-ideal monomorphism", instance]
instance toStructureSheaf_mono
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X) :
    Mono (toStructureSheaf i U) := sorry

/-- The pulled-back kernel inclusion and the kernel inclusion of the restricted morphism represent
the same ideal subobject. -/
@[stacks 01IN "restriction kernel-ideal subobject equality"]
theorem mk_eq
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X)
    {iU : Z.restrict (i.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding}
    (hiU : i.IsOpenRestriction (i.preimageOpen U) U iU) :
    Subobject.mk (toStructureSheaf i U) =
      Subobject.mk
        (RingedSpace.Hom.kernelIdealι iU.toShHom) := sorry

/-- The pulled-back kernel inclusion and the kernel inclusion of the canonical inverse-image
restriction represent the same ideal subobject. -/
@[stacks 01IN "canonical restriction kernel-ideal subobject equality"]
theorem mk_eq_preimage
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X) :
    Subobject.mk (toStructureSheaf i U) =
      Subobject.mk
        (RingedSpace.Hom.kernelIdealι
          (i.restrictToPreimageOpen U).toShHom) := sorry

/-- The canonical isomorphism from the pullback of a kernel ideal sheaf to the kernel ideal
sheaf of an explicit restriction morphism.  The subobject equality is an explicit certificate so
the resulting non-Prop `Iso` data does not hide a deferred proof. -/
@[stacks 01IN "restriction of kernel ideal sheaves"]
noncomputable def iso
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X)
    {iU : Z.restrict (i.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding}
    (hEq : Subobject.mk (toStructureSheaf i U) =
      Subobject.mk (RingedSpace.Hom.kernelIdealι iU.toShHom)) :
    (RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding).toShHom).obj
        (kernelIdealSheaf i) ≅
      kernelIdealSheaf iU :=
  Subobject.isoOfMkEqMk (toStructureSheaf i U)
    (RingedSpace.Hom.kernelIdealι iU.toShHom) hEq

/-- The canonical kernel-ideal restriction isomorphism for the inverse image of an open.  The
subobject equality is supplied by `mk_eq_preimage`, so callers do not have to rebuild its proof
certificate. -/
@[stacks 01IN "canonical restriction of kernel ideal sheaves"]
noncomputable def iso_preimage
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X) :
    (RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding).toShHom).obj
        (kernelIdealSheaf i) ≅
    kernelIdealSheaf (i.restrictToPreimageOpen U) :=
  iso i U (mk_eq_preimage i U)

/-- The hom of the canonical inverse-image restriction isomorphism is the comparison induced by
the canonical subobject equality. -/
@[simp, stacks 01IN "canonical restriction kernel-ideal isomorphism hom"]
theorem iso_preimage_hom
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X) :
    (iso_preimage i U).hom =
      Subobject.ofMkLEMk (toStructureSheaf i U)
        (RingedSpace.Hom.kernelIdealι
          (i.restrictToPreimageOpen U).toShHom) (mk_eq_preimage i U).le := sorry

/-- The canonical inverse-image restriction isomorphism identifies the pulled-back kernel
inclusion with the restricted kernel inclusion. -/
@[reassoc (attr := simp), stacks 01IN "canonical restriction kernel-ideal comparison"]
theorem iso_preimage_hom_kernelIdealι
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X) :
    (iso_preimage i U).hom ≫
        RingedSpace.Hom.kernelIdealι (i.restrictToPreimageOpen U).toShHom =
      toStructureSheaf i U := sorry

/-- The hom of the restriction isomorphism is the canonical comparison induced by equality of
the two represented subobjects. -/
@[simp, stacks 01IN "restriction kernel-ideal isomorphism hom"]
theorem iso_hom
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X)
    {iU : Z.restrict (i.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding}
    (hEq : Subobject.mk (toStructureSheaf i U) =
      Subobject.mk (RingedSpace.Hom.kernelIdealι iU.toShHom)) :
    (iso i U hEq).hom =
      Subobject.ofMkLEMk (toStructureSheaf i U)
        (RingedSpace.Hom.kernelIdealι iU.toShHom) hEq.le := sorry

/-- The canonical restriction isomorphism identifies the pulled-back kernel inclusion with the
kernel inclusion of the restricted morphism. -/
@[reassoc (attr := simp), stacks 01IN "restriction kernel-ideal comparison"]
theorem iso_hom_kernelIdealι
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (U : Opens X)
    {iU : Z.restrict (i.preimageOpen U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding}
    (hEq : Subobject.mk (toStructureSheaf i U) =
      Subobject.mk (RingedSpace.Hom.kernelIdealι iU.toShHom)) :
    (iso i U hEq).hom ≫ RingedSpace.Hom.kernelIdealι iU.toShHom =
      toStructureSheaf i U := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom.KernelIdealRestriction
