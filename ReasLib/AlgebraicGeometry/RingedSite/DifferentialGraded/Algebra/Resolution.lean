/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Colimit
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.KFlat
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat K-flat resolutions of differential graded algebra sheaves

The reusable property in the algebra-resolution construction belongs to the underlying cochain
complex: its terms are flat and it is K-flat.  This file records sequential-colimit closure at
that level and uses arbitrary ringed-topos pullback for the universal base-change consequence.
It deliberately does not identify this absolute property with flatness relative to a differential
graded algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v uX vX

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

section Resolution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

/-- A sequential colimit of differential graded algebra sheaves is K-flat with flat terms when
the underlying complex of every stage has those properties.  Only preservation of the
underlying sequential colimit is needed. -/
@[stacks 06YR "sequential differential-graded-algebra specialization"]
theorem termwiseFlat_of_sequence (A : DGA(𝒪)) (Astage : ℕ → DGA(𝒪))
    (i : ∀ n, Astage n ⟶ Astage (n + 1))
    (e : A.toComplex ≅ colimit (Functor.ofSequence i ⋙ forgetToComplex))
    (hstage : ∀ n, HomologicalComplex.KFlat.termwiseFlat (up ℤ) (Astage n).toComplex) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) A.toComplex := sorry

/-- Lemma 24.31.1 (0FU1): a sequential colimit of DG algebras whose stages are K-flat with flat
terms has the same property after every arbitrary `RingedSite.ToposHom` pullback between
commutative ringed-topos presentations in the source universes. -/
@[stacks 0FU1 "universal ringed-topos pullback property"]
theorem universallyTermwiseFlat_of_sequence (A : DGA(𝒪))
    (Astage : ℕ → DGA(𝒪)) (i : ∀ n, Astage n ⟶ Astage (n + 1))
    (e : A.toComplex ≅ colimit (Functor.ofSequence i ⋙ forgetToComplex))
    (hstage : ∀ n,
      HomologicalComplex.KFlat.termwiseFlat (up ℤ) (Astage n).toComplex) :
    RingedSite.ToposHom.modulePullbackComplex.UniversallyTermwiseFlat.{uX, vX}
      A.toComplex := sorry

/-- Lemma 24.31.1 (tag 0FU1): after any bundled ringed-site pullback, a sequential colimit of
differential graded algebra sheaves whose stages are K-flat with flat terms remains K-flat with
flat terms.  The conclusion is about the underlying pulled-back complex. -/
@[stacks 0FU1 "site-presented pullback specialization"]
theorem termwiseFlat_pullback_of_sequence
    {CX : Type uX} [Category.{vX} CX] {JX : GrothendieckTopology CX}
    [JX.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [HasWeakSheafify JX AddCommGrpCat.{max u v}]
    [JX.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {OX : Sheaf JX CommRingCat.{max u v}}
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf J 𝒪))
    [(f.modulePushforward.{max u v}).IsRightAdjoint]
    (A : DGA(𝒪)) (Astage : ℕ → DGA(𝒪))
    (i : ∀ n, Astage n ⟶ Astage (n + 1))
    (e : A.toComplex ≅ colimit (Functor.ofSequence i ⋙ forgetToComplex))
    (hstage : ∀ n, HomologicalComplex.KFlat.termwiseFlat (up ℤ) (Astage n).toComplex) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ)
      ((f.modulePullbackComplex).obj A.toComplex) := sorry

/-- The fixed-site consequence of the universal flat K-flat DG algebra resolution. -/
theorem exists_termwiseFlat_resolution (B : DGA(𝒪)) :
    ∃ (A : DGA(𝒪)) (f : A ⟶ B), QuasiIso f.hom ∧
      HomologicalComplex.KFlat.termwiseFlat (up ℤ) A.toComplex := sorry

/-- Lemma 24.31.2 (0FU2): every DG algebra sheaf admits one quasi-isomorphic DG algebra whose
underlying complex is K-flat with flat terms both before pullback and after every arbitrary
`RingedSite.ToposHom` pullback between commutative presentations in the source universes. -/
@[stacks 0FU2 "universal ringed-topos flat K-flat resolution"]
theorem exists_universallyTermwiseFlat_resolution (B : DGA(𝒪)) :
    ∃ (A : DGA(𝒪)) (f : A ⟶ B), QuasiIso f.hom ∧
      RingedSite.ToposHom.modulePullbackComplex.UniversallyTermwiseFlat.{uX, vX}
        A.toComplex := sorry

end Resolution

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
