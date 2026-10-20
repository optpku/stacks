/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 31.23.5 (1): weakly associated points map to generic points. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_weakAss_mapsTo_genericPoints :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      Set.MapsTo f.base X.weakAss (genericPoints Y) →
        LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)

/- Lemma 31.23.5 (2): a dominant morphism between integral schemes. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_isIntegral_of_isDominant :
    ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
      (f : X ⟶ Y) [IsDominant f],
        LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)

/- Lemma 31.23.5 (3): the generic point of an integral source maps to a generic point. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_isIntegral_of_map_genericPoint_mem_genericPoints :
    ∀ {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y),
      f.base (genericPoint X) ∈ genericPoints Y →
        LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)

/- Lemma 31.23.5 (4): generic points of a reduced source map to generic points. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_genericPoints_mapsTo_of_isReduced :
    ∀ {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y),
      Set.MapsTo f.base (genericPoints X) (genericPoints Y) →
        LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)

/- Lemma 31.23.5 (5): associated points of a locally Noetherian source map to generic points. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_associatedPoints_mapsTo_genericPoints :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y),
      Set.MapsTo f.base X.associatedPoints (genericPoints Y) →
        LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)

/- Lemma 31.23.5 (6): a locally Noetherian source has no embedded points and its generic points
map to generic points. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_genericPoints_mapsTo_of_noEmbeddedPoints :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y),
      X.embeddedPoints = (∅ : Set X) →
        Set.MapsTo f.base (genericPoints X) (genericPoints Y) →
          LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)

/- Lemma 31.23.5 (7): a flat morphism. -/
@[stacks 02OU] #check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_flat :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f],
      LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom)
