module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Restriction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.13.4 (1): on a Noetherian algebraic space, restriction to the complement of
the closed subspace cut out by a quasi-coherent ideal identifies the colimit of
`Hom(I^n G, F)` with `Hom(G|_U, F|_U)`. -/
@[stacks 07UM] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.idealPowerProductHomColimitToRestriction_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I]
      (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent],
      IsIso
        (AlgebraicGeometry.AlgebraicSpace.Modules.idealPowerProductHomColimitToRestriction I G F))

/- Lemma 69.13.4 (2): the structure-module specialization identifies the ideal-power Hom
colimit with sections `Hom(𝒪_U, F|_U)` on the complement of the closed subspace. -/
@[stacks 07UM] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.idealSheafPowerHomColimitToComplementSections_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I]
      (F : X.Modules) [F.IsQuasicoherent],
      IsIso
        (AlgebraicGeometry.AlgebraicSpace.Modules.idealSheafPowerHomColimitToComplementSections I F))
