module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.FiberSubscheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
  (f : X ⟶ S) [Scheme.Hom.FiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
  [ℱ.IsFiniteType] (x : X)

/- Lemma 38.3.1: for a finite-type morphism of affine schemes and a finite-type
quasicoherent module, there is a finitely presented closed subscheme whose fiber
over a chosen point is the support of the restricted module. -/
@[stacks 057Q] #check
  (AlgebraicGeometry.Scheme.Modules.exists_fiberSupportSubscheme f ℱ x :
    ∃ I : X.IdealSheafData, ∃ _ : Scheme.Hom.FinitePresentation I.subschemeι,
      ∃ 𝒢 : I.subscheme.Modules, ∃ _ : 𝒢.IsQuasicoherent, ∃ _ : 𝒢.IsFiniteType,
        Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ) ∧
          ((I.comap (f.fiberι (f x))).support : Set (f.fiber (f x))) =
            moduleSupport ((Scheme.Modules.pullback (f.fiberι (f x))).obj ℱ))

end AlgebraicGeometry.Scheme.Modules
