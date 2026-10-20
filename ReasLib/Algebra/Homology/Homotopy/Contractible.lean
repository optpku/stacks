/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Contractible homological complexes

This file isolates the shape-independent notion of a contractible homological complex.  A
specific construction should expose its contraction as data; the propositions `ExactAt` and
`Acyclic` are downstream consequences of that data.

@stack 019C
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {ι : Type w} {c : ComplexShape ι}

/-- A homological complex is contractible when its identity is homotopic to zero. -/
@[stacks 019C "contractible homological complex"]
def Contractible (K : HomologicalComplex V c) : Prop :=
  Nonempty (Homotopy (𝟙 K) 0)

namespace Contractible

/-- An explicit contraction witnesses contractibility. -/
@[stacks 019C "contractibility from an explicit contraction"]
theorem ofHomotopy {K : HomologicalComplex V c}
    (h : Homotopy (𝟙 K) 0) : K.Contractible := sorry

/-- A homological complex which is zero is contractible. -/
@[stacks 019C "contractibility of a zero homological complex"]
theorem ofIsZero {K : HomologicalComplex V c}
    (hK : IsZero K) : K.Contractible := sorry

/-- A contractible complex is exact at every degree where its homology is available. -/
@[stacks 019C "exactness of a contractible complex"]
theorem exactAt {K : HomologicalComplex V c} (hK : K.Contractible)
    (i : ι) [K.HasHomology i] : K.ExactAt i := sorry

/-- A contractible complex with homology in every degree is acyclic. -/
@[stacks 019C "acyclicity of a contractible complex"]
theorem acyclic {K : HomologicalComplex V c} (hK : K.Contractible)
    [∀ i, K.HasHomology i] : K.Acyclic := sorry

end Contractible
end HomologicalComplex

namespace Homotopy

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {ι : Type w} {c : ComplexShape ι}

/-- A zero homological complex has a canonical contraction. -/
@[stacks 019C "contraction of a zero homological complex"]
noncomputable def contractionOfIsZero {K : HomologicalComplex V c}
    (hK : IsZero K) :
    Homotopy (𝟙 K) (0 : K ⟶ K) :=
  Homotopy.ofEq (hK.eq_of_src (𝟙 K) 0)

namespace equivZero

/-- The composite through the zero complex is the zero endomorphism. -/
theorem hom_comp_inv [HasZeroObject V] (K : HomologicalComplex V c) :
    (0 : K ⟶ (HomologicalComplex.zero : HomologicalComplex V c)) ≫
        (0 : (HomologicalComplex.zero : HomologicalComplex V c) ⟶ K) =
      0 := sorry

/-- The zero endomorphism of the zero complex is its identity. -/
theorem inv_comp_hom [HasZeroObject V] (K : HomologicalComplex V c) :
    (0 : (HomologicalComplex.zero : HomologicalComplex V c) ⟶ K) ≫
        (0 : K ⟶ (HomologicalComplex.zero : HomologicalComplex V c)) =
      𝟙 (HomologicalComplex.zero : HomologicalComplex V c) := sorry

end equivZero

/-- An explicit contraction determines a homotopy equivalence with the zero complex. -/
@[stacks 019C "homotopy equivalence with zero from a contraction"]
noncomputable def equivZero [HasZeroObject V] {K : HomologicalComplex V c}
    (h : Homotopy (𝟙 K) 0) :
    HomotopyEquiv K (HomologicalComplex.zero : HomologicalComplex V c) :=
  { hom := 0
    inv := 0
    homotopyHomInvId :=
      (Homotopy.ofEq (equivZero.hom_comp_inv K)).trans h.symm
    homotopyInvHomId := Homotopy.ofEq (equivZero.inv_comp_hom K) }

end Homotopy

namespace HomotopyEquiv

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {ι : Type w} {c : ComplexShape ι}

/-- Contractibility is invariant under homotopy equivalence.

The zero object assumption supplies the canonical zero complex used by the
homotopy-equivalence interface; the statement itself is independent of any
chosen contraction.
-/
@[stacks 019C "contractibility is invariant under homotopy equivalence"]
theorem contractible_iff {K L : HomologicalComplex V c} (e : HomotopyEquiv K L) :
    K.Contractible ↔ L.Contractible := sorry

/-- Acyclicity is invariant under homotopy equivalence. -/
@[stacks 019C "acyclicity is invariant under homotopy equivalence"]
theorem acyclic_iff [CategoryWithHomology V]
    {K L : HomologicalComplex V c} (e : HomotopyEquiv K L) :
    K.Acyclic ↔ L.Acyclic := sorry

end HomotopyEquiv
