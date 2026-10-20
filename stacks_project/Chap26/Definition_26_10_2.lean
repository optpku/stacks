/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 26.10.2 (1): Mathlib defines a scheme open immersion to be an open immersion after
forgetting to locally ringed spaces. -/
@[stacks 01IO] #check @IsOpenImmersion

section

variable {X : Scheme.{u}} (U : X.Opens)

/- Definition 26.10.2 (2): the inclusion of an open subscheme is an open immersion. -/
@[stacks 01IO] #check (inferInstance : IsOpenImmersion U.ι)

end

/- Definition 26.10.2 (3): closed immersions agree before and after forgetting to locally
ringed spaces. -/
@[stacks 01IO] #check isClosedImmersion_iff_toLRSHom_isClosedImmersion

/- Definition 26.10.2 (4): the canonical closed subscheme is the closed subspace associated to
its defining ideal. -/
@[stacks 01IO] #check Scheme.IdealSheafData.isAssociated_subschemeι
#check closedSubscheme_ι_toLRSHom_isClosedImmersion

/- Definition 26.10.2 (5): an immersion is a closed immersion followed by an open immersion. -/
@[stacks 01IO] #check IsImmersion.isImmersion_iff_exists
