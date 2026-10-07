module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.Interleaving
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.LeftSystem.Derived.Interleaving
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.TensorProduct.Derived.FixedLeft
public import ReasLib.CategoryTheory.DerivedCategory.Limit.ProIsomorphism
public import ReasLib.CategoryTheory.Pro.Sequential.Interleaving
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative derived tensor and interleavings

An interleaving of global left derived module systems remains an interleaving after stagewise
relative derived tensor with a fixed right system.  The generic sequential pro-object API then
supplies a representative inverse, and derived limits of the two tensor towers are noncanonically
isomorphic.
-/

@[expose] public section

noncomputable section

universe u x v w

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.Derived.Left.Interleaving

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
variable {N N' : Left.Category.{u, x, w} A}

/-- The two tensor maps around an even stage compose to the corresponding transition of the
tensor tower. -/
theorem tensor_evenComp (z : Left.Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (i : ℕ) :
    TensorProduct.Derived.mapLeftLE M (z.evenToOdd i) ≫
        TensorProduct.Derived.mapLeftLE M (z.oddToEven i) =
      (TensorProduct.Derived.tower M N).transitionMap
        (z.reindex.monotone
          (Nat.mul_le_mul_left 2 (Nat.le_add_right i 1))) := sorry

/-- The two tensor maps around an odd stage compose to the corresponding transition of the
other tensor tower. -/
theorem tensor_oddComp (z : Left.Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (i : ℕ) :
    TensorProduct.Derived.mapLeftLE M (z.oddToEven (i + 1)) ≫
        TensorProduct.Derived.mapLeftLE M (z.evenToOdd i) =
      (TensorProduct.Derived.tower M N').transitionMap
        (z.reindex.monotone
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left 2 (Nat.le_add_right i 1)) 1)) := sorry

/-- Stagewise relative derived tensor carries an interleaving of left global derived systems
to an interleaving of sequential systems in `D(R)`. -/
@[stacks 0GZI "relative derived tensor preserves left-system interleavings"]
noncomputable def tensor (z : Left.Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A) :
    Pro.SequentialInterleaving
      (TensorProduct.Derived.tower M N) (TensorProduct.Derived.tower M N') where
  reindex := z.reindex
  strictMono := z.strictMono
  evenToOdd i :=
    TensorProduct.Derived.mapLeftLE M (z.evenToOdd i)
  oddToEven i :=
    TensorProduct.Derived.mapLeftLE M (z.oddToEven i)
  evenComp := tensor_evenComp z M
  oddComp := tensor_oddComp z M

/-- The tensor-tower morphism induced by a left-system interleaving has a representative
inverse. -/
@[stacks 0GZI "relative derived tensor interleavings induce pro-isomorphisms"]
theorem tensor_hasRepresentativeInverse (z : Left.Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A) :
    (tensor z M).hom.HasRepresentativeInverse := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): chosen derived limits of stagewise relative derived tensor
towers are noncanonically isomorphic under an interleaving of the left systems. -/
@[stacks 0GZI "noncanonical isomorphism of interleaved relative derived tensor limits"]
theorem nonemptyIso_tensorDerivedLimit (z : Left.Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {K K' : DerivedCategory (ModuleCat.{max v w} R)}
    (hK : IsDerivedLimit (TensorProduct.Derived.tower M N) K)
    (hK' : IsDerivedLimit (TensorProduct.Derived.tower M N') K') :
    Nonempty (K ≅ K') := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): chosen derived limits of stagewise relative derived tensor
towers are noncanonically isomorphic under an interleaving of the left systems. -/
@[stacks 0GZI "derived limits of interleaved relative derived tensor towers"]
theorem existsIso_tensorDerivedLimit (z : Left.Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {K K' : DerivedCategory (ModuleCat.{max v w} R)}
    (hK : IsDerivedLimit (TensorProduct.Derived.tower M N) K)
    (hK' : IsDerivedLimit (TensorProduct.Derived.tower M N') K') :
    ∃ f : K ⟶ K', IsIso f := sorry

end DifferentialGradedModule.InverseSystem.Derived.Left.Interleaving

namespace DifferentialGradedModule.InverseSystem.LeftSystem.Derived.Interleaving

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
variable {N N' : LeftSystem.{u, x, w} A}

/-- The two represented tensor maps around an even stage compose to the corresponding tensor
tower transition. -/
theorem tensor_evenComp (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (i : ℕ) :
    TensorProduct.Derived.RepresentedLeft.mapLeftLE M (z.evenToOdd i) ≫
        TensorProduct.Derived.RepresentedLeft.mapLeftLE M (z.oddToEven i) =
      (TensorProduct.Derived.RepresentedLeft.tower M N).transitionMap
        (z.reindex.monotone
          (Nat.mul_le_mul_left 2 (Nat.le_add_right i 1))) := sorry

/-- The two represented tensor maps around an odd stage compose to the corresponding transition
of the other tensor tower. -/
theorem tensor_oddComp (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (i : ℕ) :
    TensorProduct.Derived.RepresentedLeft.mapLeftLE M (z.oddToEven (i + 1)) ≫
        TensorProduct.Derived.RepresentedLeft.mapLeftLE M (z.evenToOdd i) =
      (TensorProduct.Derived.RepresentedLeft.tower M N').transitionMap
        (z.reindex.monotone
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left 2 (Nat.le_add_right i 1)) 1)) := sorry

/-- Stagewise relative derived tensor carries a derived interleaving of ordinary left module
systems to an interleaving of their represented tensor towers. -/
@[stacks 0GZI "relative derived tensor preserves represented left-system interleavings"]
noncomputable def tensor (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A) :
    Pro.SequentialInterleaving
      (TensorProduct.Derived.RepresentedLeft.tower M N)
      (TensorProduct.Derived.RepresentedLeft.tower M N') :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.Interleaving.tensor
      z.toGlobal M).transport
    (TensorProduct.Derived.RepresentedLeft.towerIso M N)
    (TensorProduct.Derived.RepresentedLeft.towerIso M N')

/-- The even-to-odd component of the canonical represented tensor interleaving is the
stagewise tensor of the source-shaped cross-index morphism. -/
@[simp]
theorem tensor_evenToOdd (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (i : ℕ) :
    (tensor z M).evenToOdd i =
      TensorProduct.Derived.RepresentedLeft.mapLeftLE M (z.evenToOdd i) := sorry

/-- The odd-to-even component of the canonical represented tensor interleaving is the
stagewise tensor of the source-shaped cross-index morphism. -/
@[simp]
theorem tensor_oddToEven (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (i : ℕ) :
    (tensor z M).oddToEven i =
      TensorProduct.Derived.RepresentedLeft.mapLeftLE M (z.oddToEven i) := sorry

/-- The represented tensor-tower morphism induced by an ordinary left-system interleaving has
a representative inverse. -/
@[stacks 0GZI "represented relative derived tensor interleavings induce pro-isomorphisms"]
theorem tensor_hasRepresentativeInverse (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A) :
    (tensor z M).hom.HasRepresentativeInverse := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): chosen derived limits of represented relative derived tensor
towers are noncanonically isomorphic. -/
@[stacks 0GZI "noncanonical isomorphism of represented relative derived tensor limits"]
theorem nonemptyIso_tensorDerivedLimit (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {K K' : DerivedCategory (ModuleCat.{max v w} R)}
    (hK : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N) K)
    (hK' : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N') K') :
    Nonempty (K ≅ K') := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): chosen derived limits of the represented relative derived
tensor towers are noncanonically isomorphic. -/
@[stacks 0GZI "derived limits of represented interleaved tensor towers"]
theorem existsIso_tensorDerivedLimit (z : Interleaving A N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {K K' : DerivedCategory (ModuleCat.{max v w} R)}
    (hK : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N) K)
    (hK' : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N') K') :
    ∃ f : K ⟶ K', IsIso f := sorry

end DifferentialGradedModule.InverseSystem.LeftSystem.Derived.Interleaving

namespace DifferentialGradedModule.InverseSystem.LeftSystem.Derived.AreProIsomorphic

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
variable {N N' : LeftSystem.{u, x, w} A}

/-- Lemma 24.35.2 (Stacks 0GZI): derived pro-isomorphic ordinary left module systems have
noncanonically isomorphic chosen derived limits after stagewise relative derived tensor. -/
@[stacks 0GZI "derived-limit invariance for derived pro-isomorphic left systems"]
theorem nonemptyIso_tensorDerivedLimit (h : AreProIsomorphic N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {K K' : DerivedCategory (ModuleCat.{max v w} R)}
    (hK : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N) K)
    (hK' : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N') K') :
    Nonempty (K ≅ K') := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): derived pro-isomorphic ordinary left module systems have
noncanonically isomorphic chosen derived limits after stagewise relative derived tensor. -/
@[stacks 0GZI "derived-limit invariance for derived pro-isomorphic left systems"]
theorem existsIso_tensorDerivedLimit (h : AreProIsomorphic N N')
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {K K' : DerivedCategory (ModuleCat.{max v w} R)}
    (hK : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N) K)
    (hK' : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N') K') :
    ∃ f : K ⟶ K', IsIso f := sorry

end DifferentialGradedModule.InverseSystem.LeftSystem.Derived.AreProIsomorphic
