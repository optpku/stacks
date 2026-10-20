/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Normal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.53.6 (1): under the stated properness, normality, reducedness, generic-point,
and generic-fibre global-sections hypotheses, the canonical map `𝒪_S ⟶ f_*𝒪_X` is an isomorphism. -/
@[stacks 0AY8] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafMap_isIso_of_genericFiberGlobalSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsProper f] [IsIntegral S] (_ : S.isNormal) [IsReduced X],
      (∀ x : X, x ∈ genericPoints X → f x = genericPoint S) →
      Function.Bijective
        (globalSectionsMap (f.fiberToSpecResidueField (genericPoint S))) →
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

/- Lemma 37.53.6 (2): under the same hypotheses, the morphism `f` has geometrically connected
fibres. -/
@[stacks 0AY8] #check
  (AlgebraicGeometry.Scheme.Hom.geometricallyConnected_of_genericFiberGlobalSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsProper f] [IsIntegral S] (_ : S.isNormal) [IsReduced X],
      (∀ x : X, x ∈ genericPoints X → f x = genericPoint S) →
      Function.Bijective
        (globalSectionsMap (f.fiberToSpecResidueField (genericPoint S))) →
      GeometricallyConnected f)

end AlgebraicGeometry.Scheme.Hom
