/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Topos
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Cartesian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/- Situation 21.38.3 (08PA): a morphism of fibred categories induces a morphism between the
inherited ringed sites, and the resulting triangle over the base ringed site commutes. -/
@[stacks 08PA "underlying functor of a fibred-category morphism"]
#check @FiberedCategoryOver.toFunctor

@[stacks 08PA "compatibility with the base projections"]
#check @FiberedCategoryOver.comm

@[stacks 08PA "cartesian-functor presentation"]
#check @FiberedCategoryOver.toCartesianBasedFunctor

@[stacks 08PA "inherited structure-sheaf isomorphism"]
#check @CartesianBasedFunctor.inheritedToposHom.structureSheafIso

@[stacks 08PA "inherited morphism of ringed topoi"]
#check @CartesianBasedFunctor.inheritedToposHom

@[stacks 08PA "commutative triangle of inherited ringed topoi"]
#check @CartesianBasedFunctor.inheritedToposHom.projectionTriangle

/- The following owners retain the stronger site-functor presentation used by localization
arguments downstream. -/
@[stacks 08PA "site-presentation structure-sheaf comparison"]
#check @Functor.inheritedStructureSheafComparison

@[stacks 08PA "site-presentation inherited morphism"]
#check @Functor.inheritedRingedSiteHom

@[stacks 08PA "inherited ringed-site base functor"]
#check @Functor.inheritedRingedSiteHom_base

@[stacks 08PA "inherited ringed-site structure-sheaf map"]
#check @Functor.inheritedRingedSiteHom_structureSheafMap

@[stacks 08PA "site-presentation commutative triangle"]
#check @Functor.inheritedRingedSiteHom_projection

@[stacks 08PA "projection composition law"]
#check @Functor.inheritedRingedSiteHom_projection_w

end CategoryTheory
