module

import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Support
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.9.3 (1): the scheme-theoretic support is contained in the closed
subscheme cut out by the zeroth Fitting ideal sheaf. -/
@[stacks 0CYX] #check
  (AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_zero_le_schemeTheoreticSupport :
    ∀ {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
      (I : S.IdealSheafData)
      (hI : AlgebraicGeometry.Scheme.Modules.IsSchemeTheoreticSupport F I),
        Scheme.fittingIdealSheaf F 0 ≤ I)

/- Lemma 31.9.3 (2): the underlying closed subset of a scheme-theoretic support
is the ordinary support of the module. -/
@[stacks 0CYX] #check
  (AlgebraicGeometry.Scheme.Modules.moduleSupport_eq_of_isSchemeTheoreticSupport :
    ∀ {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (I : S.IdealSheafData)
      (hI : AlgebraicGeometry.Scheme.Modules.IsSchemeTheoreticSupport F I),
        RingedSpace.moduleSupport F = (I.support : Set S))

/- Lemma 31.9.3 (3): the closed subscheme cut out by the zeroth Fitting ideal
sheaf has underlying closed subset equal to the ordinary support. -/
@[stacks 0CYX] #check
  (AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_zero_support_eq_moduleSupport :
    ∀ {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent],
      ((Scheme.fittingIdealSheaf F 0).support : Set S) =
        RingedSpace.moduleSupport F)

/- Lemma 31.9.3 (4): the module descends to a finite-type quasicoherent module
on the closed subscheme cut out by the zeroth Fitting ideal sheaf. -/
@[stacks 0CYX] #check
  (AlgebraicGeometry.Scheme.Modules.exists_finiteType_module_pushforward_fittingIdealSheaf_zero :
    ∀ {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent],
      ∃ G0 : (Scheme.fittingIdealSheaf F 0).subscheme.Modules,
        ∃ _ : G0.IsQuasicoherent,
          ∃ _ : G0.IsFiniteType,
            Nonempty ((Scheme.Modules.pushforward
              (Scheme.fittingIdealSheaf F 0).subschemeι).obj G0 ≅ F))
