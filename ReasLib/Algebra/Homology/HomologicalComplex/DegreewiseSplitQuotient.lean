/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.TermwiseSplit
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise-split quotients of homological complexes

A degreewise-split quotient records the quotient object and projection of a morphism together with
one splitting in every degree.  The owner is independent of the orientation and indexing type of
the complex; cochain-complex triangles are developed in a separate leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} {c : ComplexShape ι}

section Preadditive

variable [Preadditive C]

/-- A quotient row of homological complexes that is split after evaluation in every degree. -/
@[stacks 014R "degreewise-split quotient row"]
structure DegreewiseSplitQuotient {K L : HomologicalComplex C c} (f : K ⟶ L) where
  /-- The quotient complex. -/
  quotient : HomologicalComplex C c
  /-- The projection to the quotient complex. -/
  projection : L ⟶ quotient
  /-- The inclusion followed by the projection vanishes. -/
  zero : f ≫ projection = 0
  /-- A splitting of the quotient row in every degree. -/
  splitting : ∀ i : ι,
    ((ShortComplex.mk f projection zero).map (eval C c i)).Splitting

namespace DegreewiseSplitQuotient

variable {K L : HomologicalComplex C c} {f : K ⟶ L}

/-- The short complex underlying a degreewise-split quotient. -/
abbrev shortComplex (D : DegreewiseSplitQuotient f) :
    ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk f D.projection D.zero

/-- The underlying short complex is degreewise split, without retaining a chosen family. -/
theorem shortComplex_isDegreewiseSplit (D : DegreewiseSplitQuotient f) :
    D.shortComplex.IsDegreewiseSplit := sorry

/-- The first map in a degreewise-split quotient is termwise split monic. -/
theorem termwiseSplitMono (D : DegreewiseSplitQuotient f) :
    HomologicalComplex.termwiseSplitMono C c f := sorry

/-- The projection in a degreewise-split quotient is termwise split epic. -/
theorem termwiseSplitEpi (D : DegreewiseSplitQuotient f) :
    HomologicalComplex.termwiseSplitEpi C c D.projection := sorry

end DegreewiseSplitQuotient

end Preadditive

namespace DegreewiseSplitQuotient

section Abelian

variable [Abelian C]
variable {K L : HomologicalComplex C c} {f : K ⟶ L}

/-- The degreewise splitting of the cokernel row determined by explicit retractions of a
homological-complex morphism. -/
noncomputable def cokernelSplitting (f : K ⟶ L)
    (hf : ∀ i : ι, SplitMono (f.f i)) (i : ι) :
    ((ShortComplex.cokernelSequence f).map (eval C c i)).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    ((ShortComplex.cokernelSequence_exact f).map (eval C c i))
    (hf i).retraction (hf i).id
    (((shortExact_iff_degreewise_shortExact (ShortComplex.cokernelSequence f)).mp
      { exact := ShortComplex.cokernelSequence_exact f
        mono_f := mono_of_mono_f f (fun j ↦ (hf j).mono)
        epi_g := inferInstance }) i).epi_g

/-- The canonical cokernel row of a morphism equipped with explicit degreewise retractions. -/
noncomputable def ofSplitMono (f : K ⟶ L) (hf : ∀ i : ι, SplitMono (f.f i)) :
    DegreewiseSplitQuotient f where
  quotient := cokernel f
  projection := cokernel.π f
  zero := cokernel.condition f
  splitting := cokernelSplitting f hf

/-- Choose explicit degreewise retractions from the termwise split-monomorphism property. -/
noncomputable def chosenSplitMono (f : K ⟶ L)
    (hf : HomologicalComplex.termwiseSplitMono C c f) (i : ι) : SplitMono (f.f i) :=
  (hf i).exists_splitMono.some

/-- The canonical cokernel row of a termwise split monomorphism.  Its quotient and projection are
canonical; only its degreewise splitting uses the choice contained in `IsSplitMono`. -/
noncomputable def ofTermwiseSplitMono (f : K ⟶ L)
    (hf : HomologicalComplex.termwiseSplitMono C c f) : DegreewiseSplitQuotient f :=
  ofSplitMono f (chosenSplitMono f hf)

/-- The quotient object of `ofTermwiseSplitMono` is the categorical cokernel. -/
@[simp]
theorem ofTermwiseSplitMono_quotient (f : K ⟶ L)
    (hf : HomologicalComplex.termwiseSplitMono C c f) :
    (ofTermwiseSplitMono f hf).quotient = cokernel f := sorry

/-- The projection of `ofTermwiseSplitMono` is the canonical cokernel projection. -/
@[simp]
theorem ofTermwiseSplitMono_projection (f : K ⟶ L)
    (hf : HomologicalComplex.termwiseSplitMono C c f) :
    (ofTermwiseSplitMono f hf).projection = cokernel.π f := sorry

end Abelian

end DegreewiseSplitQuotient

end HomologicalComplex
