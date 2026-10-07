module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper

/-!
# Properness of scheme-theoretic support

This file relates properness of the ordinary support of a finite-type quasicoherent module to
properness of its scheme-theoretic support and to presentations by modules on proper closed
subschemes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite-type quasicoherent module on a scheme locally of finite type over a base,
properness of its ordinary support, properness of its scheme-theoretic support, and descent from
a proper closed subscheme are equivalent. -/
theorem moduleSupport_properOver_tfae_schemeTheoreticSupport_and_pushforward
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] :
    List.TFAE [
      ClosedSubset.IsProperOver f (closedSupport ℱ),
      IsProper ((schemeTheoreticSupport ℱ).subschemeι ≫ f),
      ∃ I : X.IdealSheafData,
        ∃ 𝒢 : I.subscheme.Modules,
          ∃ _ : 𝒢.IsFiniteType,
            ∃ _ : 𝒢.IsQuasicoherent,
              ∃ _ : IsProper (I.subschemeι ≫ f),
                Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ)
    ] := sorry

end AlgebraicGeometry.Scheme.Modules
