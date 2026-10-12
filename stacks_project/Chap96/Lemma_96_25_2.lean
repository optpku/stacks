/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import stacks_project.Chap96.Lemma_96_25_2_Restriction

/-!
# Lemma 96.25.2

For a category fibred in groupoids, an `𝒪`-module on `𝒳_affine` is étale
base-change compatible if and only if it is an étale sheaf with quasi-coherent
restrictions to each `U_affine,étale`, if and only if it corresponds to a
locally quasi-coherent module on `𝒳` via the ringed-topos equivalence of
96.24.3.1 at the étale topology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme
open CategoryTheory.Functor CategoryTheory.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace AffineModule

/-- An affine module is étale compatible when the canonical comparison
`F(x') ⊗[𝒪(x')] 𝒪(x) ⟶ F(x)` is an isomorphism for every morphism
`x ⟶ x'` of `𝒳_affine` lying over an étale morphism of affine schemes. -/
def EtaleCompatible {X : GroupoidsOver S} (F : AffineModule X) : Prop :=
  ∀ ⦃x x' : Affine X⦄ (f : x ⟶ x'),
    Etale (X.p.map f.hom).left → IsIso (F.baseChangeMap f)

/-- Étale compatibility is the pointwise isomorphism condition for affine
base-change maps along étale arrows. -/
theorem etaleCompatible_iff {X : GroupoidsOver S} (F : AffineModule X) :
    F.EtaleCompatible ↔
      ∀ ⦃x x' : Affine X⦄ (f : x ⟶ x'),
        Etale (X.p.map f.hom).left → IsIso (F.baseChangeMap f) :=
  sorry

/-- An affine module is an étale sheaf with quasi-coherent affine étale
restrictions when it is a sheaf for the étale topology on `𝒳_affine` and,
for every object `x` of `𝒳_affine` with `U = p(x)`, the restriction
`x* F|_{U_affine,étale}` is quasi-coherent. -/
def IsEtaleSheafWithQuasicoherentRestrictions {X : GroupoidsOver S}
    (F : AffineModule X) : Prop :=
  ∃ hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf,
    ∀ x : Affine X, (restrictToSmallAffineEtale F x hF).IsQuasicoherent

/-- The étale sheaf-with-quasi-coherent-restrictions predicate records étale
sheafhood together with quasi-coherence of every affine étale restriction. -/
theorem isEtaleSheafWithQuasicoherentRestrictions_iff {X : GroupoidsOver S}
    (F : AffineModule X) :
    F.IsEtaleSheafWithQuasicoherentRestrictions ↔
      ∃ hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf,
        ∀ x : Affine X, (restrictToSmallAffineEtale F x hF).IsQuasicoherent :=
  sorry

/-- Identification of the commutative and ring presentations of the
universe-lifted étale structure sheaf of `X`. -/
def liftedEtaleRingPresheafIso (X : GroupoidsOver S) :
    (commEtaleRingedSiteLift X).structureSheaf.obj ≅
      (liftedAssociatedStructureSheaf X .etale).obj where
  hom :=
    Functor.whiskerLeft (X.p.op ⋙ (Over.forget S).op ⋙ Scheme.Γ)
      universeLiftForget₂Iso.hom
  inv :=
    Functor.whiskerLeft (X.p.op ⋙ (Over.forget S).op ⋙ Scheme.Γ)
      universeLiftForget₂Iso.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of the commutative and ring presentations of the
universe-lifted étale structure sheaf of `X`, as sheaves of rings. -/
def liftedEtaleRingSheafIso (X : GroupoidsOver S) :
    (commEtaleRingedSiteLift X).structureSheaf ≅
      liftedAssociatedStructureSheaf X .etale where
  hom := ⟨(liftedEtaleRingPresheafIso X).hom⟩
  inv := ⟨(liftedEtaleRingPresheafIso X).inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying presheaf morphism of `liftedEtaleRingSheafIso` is
`liftedEtaleRingPresheafIso`. -/
theorem liftedEtaleRingSheafIso_hom (X : GroupoidsOver S) :
    (liftedEtaleRingSheafIso X).hom.hom =
      (liftedEtaleRingPresheafIso X).hom :=
  sorry

/-- Transport an affine étale module sheaf along the ringed-topos comparison of
96.24.3.1 at the étale topology. -/
def correspondingModule {X : GroupoidsOver S} (F : AffineModule X)
    (hF : Presheaf.IsSheaf (X.associatedAffineTopology .etale) F.presheaf) :
    SheafOfModules (liftedAssociatedStructureSheaf X .etale) :=
  (associatedAffineComparison X .etale).modulePushforward.obj
    (toAssociatedModule F hF)

/-- `correspondingModule F hF` is the module pushforward of
`toAssociatedModule F hF` along `associatedAffineComparison` at the étale
topology. -/
theorem correspondingModule_eq {X : GroupoidsOver S} (F : AffineModule X)
    (hF : Presheaf.IsSheaf (X.associatedAffineTopology .etale) F.presheaf) :
    correspondingModule F hF =
      (associatedAffineComparison X .etale).modulePushforward.obj
        (toAssociatedModule F hF) :=
  sorry

/-- Transport `correspondingModule F hF` to the commutative universe-lifted
étale ringed site of `X`. -/
def correspondingLiftedModule {X : GroupoidsOver S} (F : AffineModule X)
    (hF : Presheaf.IsSheaf (X.associatedAffineTopology .etale) F.presheaf) :
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  (SheafOfModules.restrictScalars (liftedEtaleRingSheafIso X).hom).obj
    (correspondingModule F hF)

/-- `correspondingLiftedModule` is restriction of scalars of
`correspondingModule` along `liftedEtaleRingSheafIso`. -/
theorem correspondingLiftedModule_eq {X : GroupoidsOver S} (F : AffineModule X)
    (hF : Presheaf.IsSheaf (X.associatedAffineTopology .etale) F.presheaf) :
    correspondingLiftedModule F hF =
      (SheafOfModules.restrictScalars (liftedEtaleRingSheafIso X).hom).obj
        (correspondingModule F hF) :=
  sorry

/-- An affine module corresponds to a locally quasi-coherent module on `𝒳`
via the ringed-topos equivalence of 96.24.3.1 for the étale topology. -/
def CorrespondsToLocallyQuasicoherent {X : GroupoidsOver S}
    (F : AffineModule X) : Prop :=
  ∃ hF : Presheaf.IsSheaf (X.associatedAffineTopology .etale) F.presheaf,
    IsLocallyQuasiCoherentLift (correspondingLiftedModule F hF)

/-- Correspondence records étale sheafhood on `𝒳_affine` together with local
quasi-coherence of the transported étale module. -/
theorem correspondsToLocallyQuasicoherent_iff {X : GroupoidsOver S}
    (F : AffineModule X) :
    F.CorrespondsToLocallyQuasicoherent ↔
      ∃ hF : Presheaf.IsSheaf (X.associatedAffineTopology .etale) F.presheaf,
        IsLocallyQuasiCoherentLift (correspondingLiftedModule F hF) :=
  sorry

end AffineModule

/-- Lemma 96.25.2: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. Let `F` be an `𝒪`-module on `𝒳_affine`. The following are
equivalent: for every morphism `x ⟶ x'` of `𝒳_affine` such that
`p(x) ⟶ p(x')` is an étale morphism of affine schemes, the map
`F(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ F(x)` is an isomorphism; `F` is a sheaf for the
étale topology on `𝒳_affine` and for every object `x` of `𝒳_affine` the
restriction `x* F|_{U_affine,étale}` is quasi-coherent where `U = p(x)`;
`F` corresponds to a locally quasi-coherent module on `𝒳` via the
equivalence of 96.24.3.1 for the étale topology. -/
@[stacks 0H0F]
theorem locallyQuasicoherentAffine_tfae {X : GroupoidsOver S}
    (F : AffineModule X) :
    List.TFAE
      [F.EtaleCompatible, F.IsEtaleSheafWithQuasicoherentRestrictions,
        F.CorrespondsToLocallyQuasicoherent] :=
  sorry

/-- Étale compatibility is equivalent to being an étale sheaf with
quasi-coherent affine étale restrictions. -/
theorem etaleCompatible_iff_isEtaleSheafWithQuasicoherentRestrictions
    {X : GroupoidsOver S} (F : AffineModule X) :
    F.EtaleCompatible ↔ F.IsEtaleSheafWithQuasicoherentRestrictions :=
  sorry

/-- Being an étale sheaf with quasi-coherent affine étale restrictions is
equivalent to corresponding to a locally quasi-coherent étale module via
96.24.3.1. -/
theorem isEtaleSheafWithQuasicoherentRestrictions_iff_correspondsToLocallyQuasicoherent
    {X : GroupoidsOver S} (F : AffineModule X) :
    F.IsEtaleSheafWithQuasicoherentRestrictions ↔
      F.CorrespondsToLocallyQuasicoherent :=
  sorry

/-- Étale compatibility is equivalent to corresponding to a locally
quasi-coherent étale module via 96.24.3.1. -/
theorem etaleCompatible_iff_correspondsToLocallyQuasicoherent
    {X : GroupoidsOver S} (F : AffineModule X) :
    F.EtaleCompatible ↔ F.CorrespondsToLocallyQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
