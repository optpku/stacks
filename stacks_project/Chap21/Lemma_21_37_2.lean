module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.37.2

For a continuous and cocontinuous functor of sites, module lower-shriek has a total left-derived
functor.  It is left adjoint to the exact derived inverse image and sends each localized structure
module at `U` to the localized structure module at `f.obj U`.
-/

/- Lemma 21.37.2 (07AC) (1): existence of the total left-derived lower-shriek functor. -/
@[stacks 07AC "(1) derived lower-shriek existence"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.toDerived.hasLeftDerived

/- Lemma 21.37.2 (07AC) (2): derived lower-shriek is left adjoint to the exact derived module
inverse image. -/
@[stacks 07AC "(2) exact-derived adjunction"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived.adjunction

/- Lemma 21.37.2 (07AC) (3): the derived generator calculation
`Lg_!(j_{U!} O_U) ≅ j_{f(U)!} O_{f(U)}`. -/
@[stacks 07AC "(3) derived generator isomorphism"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived.structureModuleIso

/- The exact underived owner whose action on derived categories is the canonical `g^*`. -/
#check @RingedSite.Cocontinuous.moduleInverseImage.exactFunctor

/- The intermediate underived generator calculation. -/
#check @RingedSite.Cocontinuous.moduleLowerShriek.structureModuleIso
