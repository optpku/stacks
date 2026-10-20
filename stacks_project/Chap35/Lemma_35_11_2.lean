/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.SmallAffine.Quasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

universe u

/- Lemma 35.11.2: for the small affine Zariski or étale site of `S`, base-change
compatibility, quasi-coherence, descent from the full small site, and existence of a
unique compatible quasi-coherent module on `S` are equivalent. -/
@[stacks 0GZX] #check
  (AlgebraicGeometry.SmallStandardTopology.Affine.quasicoherent_tfae :
    ∀ (τ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : PresheafOfModules.{u}
        (AlgebraicGeometry.SmallStandardTopology.Affine.structurePresheaf τ S)),
      List.TFAE [
        PresheafOfModules.BaseChange.compatible
          (AlgebraicGeometry.SmallStandardTopology.Affine.commStructurePresheaf τ S) F,
        ∃ hF : Presheaf.IsSheaf
            (AlgebraicGeometry.SmallStandardTopology.Affine.topology τ S) F.presheaf,
          (AlgebraicGeometry.SmallStandardTopology.Affine.asSheaf τ S F hF).IsQuasicoherent,
        ∃ (hF : Presheaf.IsSheaf
              (AlgebraicGeometry.SmallStandardTopology.Affine.topology τ S) F.presheaf)
            (hqc :
              (AlgebraicGeometry.SmallStandardTopology.Affine.asSheaf τ S F hF).IsQuasicoherent),
          (AlgebraicGeometry.SmallStandardTopology.Affine.qcRestriction τ S).essImage
            ⟨AlgebraicGeometry.SmallStandardTopology.Affine.asSheaf τ S F hF, hqc⟩,
        ∃ (hF : Presheaf.IsSheaf
              (AlgebraicGeometry.SmallStandardTopology.Affine.topology τ S) F.presheaf)
            (hqc :
              (AlgebraicGeometry.SmallStandardTopology.Affine.asSheaf τ S F hF).IsQuasicoherent),
          AlgebraicGeometry.SmallStandardTopology.Affine.HasUniqueSchemeModel τ S
            ⟨AlgebraicGeometry.SmallStandardTopology.Affine.asSheaf τ S F hF, hqc⟩])
