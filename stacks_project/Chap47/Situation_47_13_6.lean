/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Derived
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Scalar.Derived
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

variable {R : Type u} [CommRing R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {E : CochainDGAlgebra.{u, u} R}
variable (f : E ⟶ CochainDGAlgebra.ofAlgebra R A)
variable (hf : CochainDGAlgebra.quasiIso f)

/- Situation 47.13.6 (1): a quasi-isomorphism `E ⟶ A`, with `A` regarded as a
degree-zero cochain DGA, induces a categorical equivalence between `D(E)` and `D(A)`. -/
@[stacks 0BZB] #check
  (CochainDGAlgebra.Hom.Derived.equivalence f hf :
    DifferentialGradedModule.Derived.Category E ≌
      DifferentialGradedModule.Derived.Category (CochainDGAlgebra.ofAlgebra R A))

/- Situation 47.13.6 (2): restriction along `E ⟶ A` commutes, up to the canonical
natural isomorphism, with restriction to the base ring `R`. -/
@[stacks 0BZB] #check
  (CochainDGAlgebra.Hom.Derived.restrictionCompFromBaseIso f :
    CochainDGAlgebra.Hom.Derived.restriction.{u, u, u, u} f ⋙
        CochainDGAlgebra.Hom.Derived.restriction.{u, u, u, u}
          (CochainDGAlgebra.Hom.fromBase E) ≅
      CochainDGAlgebra.Hom.Derived.restriction.{u, u, u, u}
        (CochainDGAlgebra.Hom.fromBase (CochainDGAlgebra.ofAlgebra R A)))

/- Situation 47.13.6 (3): derived extension from `R` to `E` and then along `E ⟶ A`
is canonically isomorphic to derived extension directly from `R` to `A`. -/
@[stacks 0BZB] #check
  (CochainDGAlgebra.Hom.Derived.extensionCompFromBaseIso f :
    CochainDGAlgebra.Hom.Derived.extension.{u, u} (CochainDGAlgebra.Hom.fromBase E) ⋙
        CochainDGAlgebra.Hom.Derived.extension.{u, u} f ≅
      CochainDGAlgebra.Hom.Derived.extension.{u, u}
        (CochainDGAlgebra.Hom.fromBase (CochainDGAlgebra.ofAlgebra R A)))
