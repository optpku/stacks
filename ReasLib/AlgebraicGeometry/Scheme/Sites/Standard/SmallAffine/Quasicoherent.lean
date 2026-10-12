/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.SmallAffine.Module

/-!
# Quasi-coherent modules on small affine Zariski and étale sites

This module relates objectwise base change, quasi-coherence on a small affine site, descent from
the corresponding full small site, and quasi-coherent models on the underlying scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology.Affine

/-- Base-change compatibility is equivalent to sheafhood and quasi-coherence on the selected
small affine site. -/
theorem baseChangeCompatible_iff_isQuasicoherent
    (τ : SmallStandardTopology) (S : Scheme.{u})
    (F : PresheafOfModules.{u} (structurePresheaf τ S)) :
    PresheafOfModules.BaseChange.compatible (commStructurePresheaf τ S) F ↔
      ∃ hF : Presheaf.IsSheaf (topology τ S) F.presheaf,
        (asSheaf τ S F hF).IsQuasicoherent := sorry

/-- An affine module presheaf is a quasi-coherent sheaf exactly when its bundled affine module
descends from the corresponding full small site. -/
theorem isQuasicoherent_iff_smallModel
    (τ : SmallStandardTopology) (S : Scheme.{u})
    (F : PresheafOfModules.{u} (structurePresheaf τ S)) :
    (∃ hF : Presheaf.IsSheaf (topology τ S) F.presheaf,
        (asSheaf τ S F hF).IsQuasicoherent) ↔
      ∃ (hF : Presheaf.IsSheaf (topology τ S) F.presheaf)
          (hqc : (asSheaf τ S F hF).IsQuasicoherent),
        (qcRestriction τ S).essImage ⟨asSheaf τ S F hF, hqc⟩ := sorry

/-- Descent from the corresponding full small site is equivalent to existence of a unique
compatible quasi-coherent module on the scheme. -/
theorem smallModel_iff_uniqueSchemeModel
    (τ : SmallStandardTopology) (S : Scheme.{u})
    (F : PresheafOfModules.{u} (structurePresheaf τ S)) :
    (∃ (hF : Presheaf.IsSheaf (topology τ S) F.presheaf)
        (hqc : (asSheaf τ S F hF).IsQuasicoherent),
      (qcRestriction τ S).essImage ⟨asSheaf τ S F hF, hqc⟩) ↔
      ∃ (hF : Presheaf.IsSheaf (topology τ S) F.presheaf)
          (hqc : (asSheaf τ S F hF).IsQuasicoherent),
        HasUniqueSchemeModel τ S ⟨asSheaf τ S F hF, hqc⟩ := sorry

/-- For a module presheaf on a small affine Zariski or étale site, objectwise base-change
compatibility, sheafhood with quasi-coherence, descent from the full small site, and existence of
a unique compatible quasi-coherent scheme model are equivalent. -/
theorem quasicoherent_tfae (τ : SmallStandardTopology) (S : Scheme.{u})
    (F : PresheafOfModules.{u} (structurePresheaf τ S)) :
    List.TFAE [
      PresheafOfModules.BaseChange.compatible (commStructurePresheaf τ S) F,
      ∃ hF : Presheaf.IsSheaf (topology τ S) F.presheaf,
        (asSheaf τ S F hF).IsQuasicoherent,
      ∃ (hF : Presheaf.IsSheaf (topology τ S) F.presheaf)
          (hqc : (asSheaf τ S F hF).IsQuasicoherent),
        (qcRestriction τ S).essImage ⟨asSheaf τ S F hF, hqc⟩,
      ∃ (hF : Presheaf.IsSheaf (topology τ S) F.presheaf)
          (hqc : (asSheaf τ S F hF).IsQuasicoherent),
        HasUniqueSchemeModel τ S ⟨asSheaf τ S F hF, hqc⟩] := sorry

end AlgebraicGeometry.SmallStandardTopology.Affine
