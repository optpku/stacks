/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import stacks_project.Chap60.Lemma_60_25_4_AlphaP
public import stacks_project.Chap60.Lemma_60_25_4_Linearization
public import stacks_project.Chap60.Proposition_60_23_1_Pushforward
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable {X' : Scheme.{u}} (x'₀ : X' ⟶ I.subscheme)
variable (f : X' ⟶ X)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/-- Lemma 60.25.4: let `p` be a prime and `(S, I, γ)` a divided-power scheme over
`ℤ_(p)` with `p ∈ I`. Set `S₀ = V(I) ⊂ S`, identified with `I.subscheme`. Let
`f : X' ⟶ X` be an iterated `α_p`-cover of schemes over `S₀` of constant degree
`q`. Let `F` be a crystal in quasi-coherent sheaves on `Cris(X/S)`, and write
`F' = f_cris^* F`. In any distinguished triangle
`Ru_{X/S,*} F ⟶ f_* Ru_{X'/S,*} F' ⟶ E ⟶ Ru_{X/S,*} F[1]` whose first map is
`linearizationComparison` (the unit-derived map `Ru F ⟶ Ru(f_cris_* F')`,
identified with `f_* Ru F'` by `linearizationComparison_zariskiPushforward_iso`),
every cohomology sheaf of the cone object `E` is annihilated by `q`. -/
@[stacks 07Q9]
theorem iteratedAlphaPCover_linearization_cone_nsmul
    (q : ℕ)
    (h_p_mem : ∀ V : S.affineOpens, (p : Γ(S, V)) ∈ I.ideal V)
    (h_over : f ≫ x₀ = x'₀)
    [Scheme.IsCharP X p] [Scheme.IsCharP X' p]
    [IsIteratedAlphaPCover p f] [IsFiniteLocallyFreeOfRank f q]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
      HasWeakSheafify
        ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U)
        AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
      ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p))
    [IsCrystalInQuasiCoherentModules F]
    {E : DerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})}
    (g :
      derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
          ((crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f
              h_over h_p').obj
            (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) ⟶
        E)
    (δ :
      E ⟶
        (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
            ((SheafOfModules.toSheaf _).obj F))⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk
          (linearizationComparison I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F) g δ ∈
        distTriang (DerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}))) :
    ∀ i : ℤ,
      (q : ℤ) • 𝟙
        ((DerivedCategory.homologyFunctor
            (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}) i).obj E) = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
