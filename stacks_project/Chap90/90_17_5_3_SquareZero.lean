/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Kernel
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZero
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Square-zero algebras and annihilated kernels
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
  (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
variable (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I]

#check (ArtinianLocalAlgCat.kerModule f h_ann : Type u)

#check (ArtinianLocalAlgCat.kerModule_smul_eq f h_ann :
  ∀ (c : k) (r : A'.carrier), A'.residueFieldIso (IsLocalRing.residue A'.carrier r) = c →
    ∀ (i : ArtinianLocalAlgCat.kerModule f h_ann), (c • i).1 = r * i.1)

#check (ArtinianLocalAlgCat.squareZero Λ k I : ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.squareZeroToResidue Λ k I :
  ArtinianLocalAlgCat.squareZero Λ k I ⟶ ArtinianLocalAlgCat.residue Λ k)

#check (ArtinianLocalAlgCat.squareZeroToResidue_spec Λ k I :
  IsLocalHom (ArtinianLocalAlgCat.squareZeroToResidue Λ k I).hom ∧
    ArtinianLocalAlgCat.residueCompat (ArtinianLocalAlgCat.squareZeroToResidue Λ k I).hom
        (ArtinianLocalAlgCat.squareZeroToResidue Λ k I).isLocalHom =
      ArtinianLocalAlgCat.residueIsoHom (ArtinianLocalAlgCat.squareZero Λ k I))
