module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap74.Lemma_74_5_1_Affine

/-!
# Lemma 74.5.1

For a module presheaf on the affine étale site of an algebraic space, objectwise
base-change compatibility, quasi-coherence on `(X_affine,étale, 𝒪_X)`, and
correspondence with a quasi-coherent module on `X` are equivalent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.AffineEtale

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineEtale

/-- Lemma 74.5.1: let `S` be a scheme, let `X` be an algebraic space over `S`, and
let `F` be a presheaf of `𝒪_X`-modules on `X_affine,étale`. The following are
equivalent: for every morphism `U ⟶ U'` of `X_affine,étale` the map
`F(U') ⊗_{𝒪_X(U')} 𝒪_X(U) ⟶ F(U)` is an isomorphism; `F` is a quasi-coherent
module on the ringed site `(X_affine,étale, 𝒪_X)` in the sense of
`SheafOfModules.IsQuasicoherent`; and `F` corresponds to a quasi-coherent module
on `X` via `affineEtaleComparison`. -/
@[stacks 0H04]
theorem quasicoherent_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    List.TFAE [baseChangeCompatible F, isQuasicoherent F, correspondsToQuasiCoherent F] :=
  sorry

/-- Objectwise base-change compatibility is equivalent to quasi-coherence on the
affine étale ringed site. -/
theorem baseChangeCompatible_iff_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    baseChangeCompatible F ↔ isQuasicoherent F :=
  sorry

/-- Quasi-coherence on the affine étale ringed site is equivalent to correspondence
with a quasi-coherent module on `X`. -/
theorem isQuasicoherent_iff_correspondsToQuasiCoherent {S : Scheme.{u}}
    {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    isQuasicoherent F ↔ correspondsToQuasiCoherent F :=
  sorry

/-- Objectwise base-change compatibility is equivalent to correspondence with a
quasi-coherent module on `X`. -/
theorem baseChangeCompatible_iff_correspondsToQuasiCoherent {S : Scheme.{u}}
    {X : AlgebraicSpace S}
    (F : PresheafOfModules.{u} (ringPresheafOfComm (commStructurePresheaf X))) :
    baseChangeCompatible F ↔ correspondsToQuasiCoherent F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AffineEtale
