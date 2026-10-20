module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 29.21.7

Finite presentation of a closed immersion is detected by finite type of its kernel ideal sheaf.

@stack 01TV
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 29.21.7: a closed immersion is of finite presentation exactly when its kernel ideal
sheaf is of finite type. -/
@[stacks 01TV] #check
  (@AlgebraicGeometry.closedImmersion_finitePresentation_iff_idealSheaf_isFiniteType :
    ∀ {X Z : Scheme.{u}} {i : Z ⟶ X}, IsClosedImmersion i →
      (Scheme.Hom.FinitePresentation i ↔
        SheafOfModules.IsFiniteType (RingedSpace.Hom.idealSheaf i.toShHom)))

end AlgebraicGeometry
