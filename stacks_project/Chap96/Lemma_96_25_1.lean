module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Affine.Quasicoherent
import StacksCheckRecall

/-!
# Lemma 96.25.1

Cartesianness of an `𝒪`-module on `𝒳_affine` is equivalent to quasi-coherence
on the chaotic affine site, to being a `τ`-sheaf and quasi-coherent for each
standard topology `τ`, and to corresponding to a quasi-coherent module on `𝒳`
via the ringed-topos equivalence of 96.24.3.1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Lemma 96.25.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
Let `F` be an `𝒪`-module on `𝒳_affine`. The following are equivalent: for every
morphism `x ⟶ x'` of `𝒳_affine` the map `F(x') ⊗[𝒪(x')] 𝒪(x) ⟶ F(x)` is an
isomorphism; `F` is a quasi-coherent module on `(𝒳_affine, 𝒪)` in the sense of
Modules on Sites, Definition 18.23.1; `F` is a sheaf for the Zariski topology
on `𝒳_affine` and a quasi-coherent module on `(𝒳_affine,Zar, 𝒪)`; the same as
in (3) for the étale, smooth, syntomic, and fppf topologies; and `F` corresponds
to a quasi-coherent module on `𝒳` via the equivalence (96.24.3.1). -/
@[stacks 0H0E] #check (AlgebraicGeometry.GroupoidsOver.AffineModule.isCartesian_tfae :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F : AffineModule X),
    List.TFAE
      [F.IsCartesian, F.IsQuasicoherent, F.IsQuasicoherentFor .zariski,
        F.IsQuasicoherentFor .etale, F.IsQuasicoherentFor .smooth,
        F.IsQuasicoherentFor .syntomic, F.IsQuasicoherentFor .fppf,
        F.CorrespondsToQuasicoherent])

#check (AlgebraicGeometry.GroupoidsOver.AffineModule.isCartesian_iff_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F : AffineModule X),
    F.IsCartesian ↔ F.IsQuasicoherent)

#check (AlgebraicGeometry.GroupoidsOver.AffineModule.isCartesian_iff_isQuasicoherentFor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F : AffineModule X)
    (τ : StandardTopology), F.IsCartesian ↔ F.IsQuasicoherentFor τ)

#check (AlgebraicGeometry.GroupoidsOver.AffineModule.isCartesian_iff_correspondsToQuasicoherent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F : AffineModule X),
    F.IsCartesian ↔ F.CorrespondsToQuasicoherent)
