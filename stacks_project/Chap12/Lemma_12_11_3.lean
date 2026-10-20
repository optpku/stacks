/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.SerreQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/- The two maps in the Grothendieck-group localization sequence are owned by the inclusion and
quotient exact functors, without source-specific environment changes. -/
#check (inclusionK0 P : AbelianK0 P.FullSubcategory →+ AbelianK0 A)
#check (quotientK0 P : AbelianK0 A →+ AbelianK0 P.isoModSerre.Localization)

/- Lemma 12.11.3 (1a) [02MX]: the image of `K₀(P) → K₀(A)` is the kernel of the map
to the Serre quotient. -/
@[stacks 02MX]
#check (k0_exact P : Function.Exact (inclusionK0 P) (quotientK0 P))

/- Lemma 12.11.3 (1b) [02MX]: the map on `K₀` induced by the Serre quotient is surjective. -/
@[stacks 02MX]
#check (quotientK0_surjective P : Function.Surjective (quotientK0 P))

variable (x : AbelianK0 P.FullSubcategory)

/- Lemma 12.11.3 (2) [02MX]: a class is in the kernel of `K₀(P) → K₀(A)` exactly when it
is the difference of the degree-`0` and degree-`1` homology classes of a two-periodic
endomorphism complex which becomes acyclic in the Serre quotient.  The bundled
`TwoPeriodicEndomorphism` contains precisely the source data `M`, `φ`, `ψ`, `φ ≫ ψ = 0`, and
`ψ ≫ φ = 0`. -/
@[stacks 02MX]
#check (mem_ker_inclusionK0_iff P x :
  x ∈ (inclusionK0 P).ker ↔
    ∃ K : TwoPeriodicEndomorphism A,
      ∃ hQ : ((P.isoModSerre.Q.mapHomologicalComplex (up (ZMod 2))).obj
        K.toCochainComplex).Acyclic,
        x = K₀[acyclicHomology P hQ 0] - K₀[acyclicHomology P hQ 1])

end CategoryTheory.ObjectProperty.SerreClassLocalization
