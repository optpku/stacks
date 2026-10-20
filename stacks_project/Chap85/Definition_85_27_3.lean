/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_27_3_Nerve
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Definition 85.27.3: the simplicial scheme associated to a morphism of schemes `f : X ⟶ S`,
denoted `(X/S)_•`, is the functor `Δᵒᵖ ⥤ Scheme` sending `[n]` to the `(n + 1)`-fold fibre
product of `X` over `S`, i.e. the Čech nerve of `f`. -/
@[stacks 024A] #check (AlgebraicGeometry.Scheme.Hom.simplicialScheme :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → SimplicialObject Scheme.{u})

#check Arrow.cechNerve.degreeZero.iso (Arrow.mk f)
#check Arrow.cechNerve.degreeOne.face_zero_iso_hom (Arrow.mk f)
#check Arrow.cechNerve.degreeOne.face_one_iso_hom (Arrow.mk f)
#check Arrow.cechNerve.degreeOne.diagonal (Arrow.mk f)
#check Arrow.cechNerve.degreeOne.diagonal_fst (Arrow.mk f)
#check Arrow.cechNerve.degreeOne.diagonal_snd (Arrow.mk f)
