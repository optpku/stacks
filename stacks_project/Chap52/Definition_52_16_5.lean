/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Situation_52_16_1
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import Mathlib.CategoryTheory.EssentialImage
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

variable (S : AffineAlgebraizationSetup A)
variable (F : Scheme.CoherentFormalModules S.U.toScheme
  ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))

/- Definition 52.16.5: a coherent formal module `F` on `U` extends to `X` when there is
   a coherent formal module `G` on `X` whose restriction is isomorphic to `F`; equivalently,
   `F` belongs to the essential image of the coherent-formal-module restriction functor. -/
@[stacks 0EIM] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.extendsTo
    (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F : Prop)
