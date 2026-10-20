module

public import stacks_project.Chap91.Lemma_91_2_3
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne
public import ReasLib.RingTheory.RingHom.SquareZero.Presentation
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

universe u

/-!
# Ext¹ of a polynomial presentation and the class of a square-zero algebra extension

For a polynomial presentation α : P → B of an A-algebra B, Ext¹_B(NL(α), N) is
the Hom-coker of G.toExtension.cotangentComplex. A square-zero A-algebra
extension of B by N lifts α through B' → B, and algebraExtensionEquiv sends
the extension to the resulting class of J/J² → N.
-/

/- Remark 91.2.4 (1) Let A → B and N be as in Lemma 91.2.3. Let α : P → B be a
presentation of B over A. With J = Ker(α), the naive cotangent complex is
G.toExtension.cotangentComplex : J/J² → Ω[P⁄A] ⊗[P] B, and its Ext¹ group is
the displayed Hom-cokernel. -/
@[stacks 0GPU] #check (RingHom.SquareZeroExtension.extOneOf_eq_zero_iff :
  ∀ {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {ι : Type u}
    (G : Algebra.Generators A B ι)
    (f : G.toExtension.Cotangent →ₗ[B] N),
    RingHom.SquareZeroExtension.extOneOf_mk G N f = 0 ↔
      ∃ g : G.toExtension.CotangentSpace →ₗ[B] N,
        f = g ∘ₗ G.toExtension.cotangentComplex)

/- Remark 91.2.4 (2) A square-zero A-algebra extension 0 → N → B' → B → 0 as in
Lemma 91.2.3 lifts α to an A-algebra map P → B'. The restriction of the lift to
J factors through J/J² → N, and the classification equivalence sends the
extension to that class in the displayed cokernel. -/
@[stacks 0GPU] #check (RingHom.SquareZeroExtension.algebraExtensionEquiv_symm_eq_conormalClass :
  ∀ {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @RingHom.SquareZeroExtension.Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _
      (RingHom.SquareZeroExtension.zeroKernelMap A B N) _),
    (RingHom.SquareZeroExtension.algebraExtensionEquiv A B N).symm
        (RingHom.SquareZeroExtension.isoClassMk S) =
      RingHom.SquareZeroExtension.compareToSelf G N
        (RingHom.SquareZeroExtension.conormalClass G S))
