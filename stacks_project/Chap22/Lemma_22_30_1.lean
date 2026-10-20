/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)

/- Lemma 22.30.1 (0FQQ): internal Hom from a differential graded bimodule is a differential
graded functor; it canonically induces functors on closed degree-zero morphisms and on homotopy
classes. -/
@[stacks 0FQQ] #check
  (DifferentialGradedBimodule.internalHomDgFunctor N :
    DgFunctor R (DifferentialGradedModule B) (DifferentialGradedModule A))
#check ((DifferentialGradedBimodule.internalHomDgFunctor N).mapComp :
  Comp R (DifferentialGradedModule B) ⥤ Comp R (DifferentialGradedModule A))
#check ((DifferentialGradedBimodule.internalHomDgFunctor N).mapK :
  K R (DifferentialGradedModule B) ⥤ K R (DifferentialGradedModule A))

/- Passing a mapped closed degree-zero morphism to the homotopy category agrees with mapping its
homotopy class directly. -/
#check DgFunctor.mapK_map_inK (DifferentialGradedBimodule.internalHomDgFunctor N)
