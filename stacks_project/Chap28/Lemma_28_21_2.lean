module

public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-!
# Lemma 28.21.2 compatibility entry point

The affine-cover and affine-scheme criteria for local projectivity are owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Affine`.
-/

#check
  (AlgebraicGeometry.Scheme.Modules.IsLocallyProjective :
    ∀ {X : Scheme.{u}}, X.Modules → Prop)

/- Lemma 28.21.2: a quasi-coherent scheme module is locally projective exactly when its
sections are projective on the members of some affine open cover. -/
@[stacks 05JQ] #check
  (AlgebraicGeometry.Scheme.Modules.isLocallyProjective_iff_exists_affineOpenCover_projectiveSections :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsLocallyProjective ℱ ↔
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            Module.Projective (Γ(X, (𝒰.f i).opensRange)) (Γ(ℱ, (𝒰.f i).opensRange)))

#check
  (AlgebraicGeometry.Scheme.Modules.tilde_isLocallyProjective_iff_module_projective :
    ∀ {R : CommRingCat.{u}} (M : ModuleCat R),
      IsLocallyProjective (tilde M) ↔ Module.Projective R M)

#check
  (AlgebraicGeometry.Scheme.Modules.instIsLocallyProjectiveTilde :
    ∀ {R : CommRingCat.{u}} (M : ModuleCat R) [Module.Projective R M],
      IsLocallyProjective (tilde M))

end AlgebraicGeometry.Scheme.Modules
