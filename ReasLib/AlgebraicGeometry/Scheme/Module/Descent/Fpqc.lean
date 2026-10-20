/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Canonical
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc descent of quasi-coherent modules

Quasi-coherent modules satisfy effective descent along arbitrary fpqc covering
families of schemes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.QCoh

variable {S : Scheme.{u}} {ι : Type v} {family : ι → Over S}

namespace canonicalFunctor

/-- The canonical functor to quasi-coherent descent data along an fpqc covering family is
fully faithful. -/
theorem fullyFaithful_of_fpqcCovering
    (hfamily : Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      Scheme.fpqcPrecoverage.coverings S) :
    Nonempty
      (QCoh.canonicalFunctor (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).FullyFaithful := sorry

end canonicalFunctor

namespace DescentData

/-- Every quasi-coherent descent datum along an fpqc covering family is effective. -/
theorem isEffective_of_fpqcCovering
    (hfamily : Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      Scheme.fpqcPrecoverage.coverings S)
    (D : QCoh.DescentData (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :
    D.IsEffective := sorry

end DescentData

end AlgebraicGeometry.Scheme.QCoh
