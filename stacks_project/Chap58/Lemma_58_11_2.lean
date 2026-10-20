module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Normalization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 58.11.2 (1): a connected finite étale morphism to a normal integral scheme has integral
source. -/
@[stacks 0BQL] #check (AlgebraicGeometry.Scheme.Hom.isIntegralOfFiniteEtaleOfConnected :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral X] (hX : X.isNormal)
    [IsFinite f] [Etale f] [ConnectedSpace Y], IsIntegral Y)

/- Lemma 58.11.2 (2): the source of the finite étale morphism is normal when the target is normal,
via the canonical weakly étale normality theorem. -/
@[stacks 0BQL] #check (AlgebraicGeometry.WeaklyEtale.isNormal :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f], Y.isNormal → X.isNormal)

/- Lemma 58.11.2 (3): a connected finite étale cover of a normal integral scheme is its
normalization in the source function field. -/
@[stacks 0BQL] #check
  (AlgebraicGeometry.Scheme.Hom.isIso_normalizationDescFunctionFieldExtension :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral X] (hX : X.isNormal)
      [IsFinite f] [Etale f] [ConnectedSpace Y],
      -- Local instance justification (defeq pin): use the derived integrality instance to identify the source function field and normalization comparison.
      letI : IsIntegral Y :=
        AlgebraicGeometry.Scheme.Hom.isIntegralOfFiniteEtaleOfConnected f hX
      let h_generic :=
        AlgebraicGeometry.Scheme.Hom.mapGenericPoint_eq_of_finiteEtaleOfConnected f hX
      let q := @Scheme.FunctionFieldExtension.map X _ Y.functionField _
        (f.functionFieldAlgebra h_generic)
      IsIso (q.normalizationDesc (Y.fromSpecStalk (genericPoint Y)) f
        (functionFieldExtensionMap_eq f h_generic)))
