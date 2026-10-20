/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/-!
# Definition 34.7.8

This chapter entry identifies the big affine fppf site inside a chosen big
fppf presentation, together with its ambient slice topology and finite
standard fppf precoverage.
-/

/- Definition 34.7.8: the big affine fppf site over `S` in a chosen big fppf
presentation has affine objects and finite standard fppf covering families
which cover in the ambient slice. -/
@[stacks 021S] #check
  (AlgebraicGeometry.ChosenBigFppfSite.bigAffineTopology.{u, v} :
    (X : AlgebraicGeometry.ChosenBigFppfSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology
          (AlgebraicGeometry.ChosenBigFppfSite.bigAffineSite X S))

#check AlgebraicGeometry.ChosenBigFppfSite.bigTopology
#check AlgebraicGeometry.ChosenBigFppfSite.bigAffineSite
#check AlgebraicGeometry.ChosenBigFppfSite.bigAffineStandardPrecoverage
#check AlgebraicGeometry.ChosenBigFppfSite.mem_bigAffineStandardPrecoverage_iff
