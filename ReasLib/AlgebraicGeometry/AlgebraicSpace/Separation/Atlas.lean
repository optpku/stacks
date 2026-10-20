module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Absolute quasi-separatedness from étale atlases

A quasi-separated scheme giving a surjective étale atlas with a quasi-compact
kernel-pair projection makes the algebraic space absolutely quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective étale atlas from a quasi-separated scheme with either
kernel-pair projection quasi-compact makes an algebraic space absolutely
quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_etale_atlas
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [QuasiSeparatedSpace U.left] (φ : ofOver U ⟶ X)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf φ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    (h_qc : QuasiCompact (kernelPair φ h_etale.rep).t.left ∨
      QuasiCompact (kernelPair φ h_etale.rep).s.left) :
    IsAbsolutelyQuasiSeparated X := sorry

end AlgebraicGeometry.AlgebraicSpace
