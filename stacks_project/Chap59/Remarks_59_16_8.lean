/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Amitsur.Acyclic
public import ReasLib.Algebra.Module.DescentDatum.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B]

/- Remarks 59.16.8 (1): for a faithfully flat map A → B, the coefficient-free
extended Amitsur cochain complex is acyclic, giving
exactness of the associated Cech complex in positive degrees. -/
@[stacks 03OE] #check (Algebra.Amitsur.extended.acyclicOfFaithfullyFlat A B A :
  (Algebra.Amitsur.extended A B A).Acyclic)

/- Remarks 59.16.8 (2): a descent datum along a faithfully flat algebra is
reconstructed from its degree-zero invariant module. -/
@[stacks 03OE] #check
  (Module.DescentDatum.reconstruction_isIso_of_faithfullyFlat :
    ∀ {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.FaithfullyFlat R A] [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : Module.DescentDatum R A N),
      CategoryTheory.IsIso D.reconstruction)

/- Remarks 59.16.8 (2): the corresponding base-ring module is the kernel of
the map n ↦ 1 ⊗ n − D.equiv (n ⊗ 1). -/
@[stacks 03OE] #check
  (Module.DescentDatum.mem_h0Module_iff :
    ∀ {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : Module.DescentDatum R A N) (n : N),
      n ∈ D.h0Module ↔
        (1 : A) ⊗ₜ[R] n = D.equiv (n ⊗ₜ[R] (1 : A)))
