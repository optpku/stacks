module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Affine
public import Mathlib.Data.List.TFAE

/-!
# Quasi-coherence criteria for affine modules

Cartesianness of a module presheaf on the affine objects of a category fibred
in groupoids is equivalent to quasi-coherence on the chaotic site, to sheafhood
and quasi-coherence for each standard topology, and to quasi-coherence after
the canonical affine ringed-topos comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

namespace AlgebraicGeometry.GroupoidsOver.AffineModule

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Cartesianness is equivalent to chaotic quasi-coherence on `(𝒳_affine, 𝒪)`. -/
theorem isCartesian_iff_isQuasicoherent (F : AffineModule X) :
    F.IsCartesian ↔ F.IsQuasicoherent :=
  sorry

/-- Cartesianness is equivalent to being a `τ`-sheaf and quasi-coherent on the
associated affine `τ`-site. -/
theorem isCartesian_iff_isQuasicoherentFor (F : AffineModule X)
    (τ : StandardTopology) :
    F.IsCartesian ↔ F.IsQuasicoherentFor τ :=
  sorry

/-- Cartesianness is equivalent to corresponding to a quasi-coherent module on
`𝒳` via the canonical affine ringed-topos comparison. -/
theorem isCartesian_iff_correspondsToQuasicoherent (F : AffineModule X) :
    F.IsCartesian ↔ F.CorrespondsToQuasicoherent :=
  sorry


/-- For a module presheaf on the affine objects of a category fibred in groupoids,
the following are equivalent: cartesianness; quasi-coherence on the chaotic
site; sheafhood and quasi-coherence for each of the Zariski, étale, smooth,
syntomic, and fppf topologies; and correspondence to a quasi-coherent module
under the canonical affine ringed-topos comparison. -/
@[stacks 0H0E]
theorem isCartesian_tfae (F : AffineModule X) :
    List.TFAE
      [F.IsCartesian, F.IsQuasicoherent, F.IsQuasicoherentFor .zariski,
        F.IsQuasicoherentFor .etale, F.IsQuasicoherentFor .smooth,
        F.IsQuasicoherentFor .syntomic, F.IsQuasicoherentFor .fppf,
        F.CorrespondsToQuasicoherent] :=
  sorry

end AlgebraicGeometry.GroupoidsOver.AffineModule
