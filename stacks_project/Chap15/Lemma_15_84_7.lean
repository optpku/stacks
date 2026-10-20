/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.FilteredColimit
import StacksCheckRecall

/-!
@stack 0DHX

Repository source label: Lemma 15.84.7.  In the current Stacks numbering this is Lemma 15.85.7
(Stacks `0DHX`), exposed through the shared filtered scalar-extension owners.
In the source notation, `R = colimᵢ Rᵢ`, `R₀ → A₀` is flat and finitely presented,
`Aᵢ = A₀ ⊗[R₀] Rᵢ`, and `A = A₀ ⊗[R₀] R`.  An `R`-perfect object `K` in `D(A)` descends
to an `Rᵢ`-perfect `Kᵢ` in `D(Aᵢ)` with
`K ≅ Kᵢ ⊗[Aᵢ]^L A`.  For `K₀, L₀ ∈ D(A₀)`, with `K₀` pseudo-coherent and `L₀` of finite
Tor dimension over `R₀`, the canonical stage Hom maps form a filtered colimit onto the target
Hom set.  The canonical stage maps and their filtered-colimit statement are exposed by
`RelativeDiagram.Rooted.homDiagram_isColimit_exists`; source-faithful factorization and
eventual-equality statements are owned directly by `RelativeDiagram.Rooted.hom_factor` and
`RelativeDiagram.Rooted.hom_eventually_eq`.  The generic
`FilteredColimit.CategoryColimit` interface only packages a supplied category-valued colimit
certificate; it is not used to weaken the source statement.

The chapter file contains no ring/tensor constructors, local instances, or model proofs.  A caller
instantiates `RelativeDiagram` with the tensor-stage system above and supplies its two colimit
cocones and explicit relative algebra maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ModuleCat.DerivedExtension

universe u v w

/- Lemma 15.85.7 (Stacks `0DHX`) (1): relative-perfect objects descend to a stage. -/
@[stacks 0DHX "relative-perfect object descent"]
#check fun {I : Type v} [Category.{w} I]
    {D : RelativeDiagram.{u, v, w} (I := I)} (S : D.Rooted) [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone) (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin))
    {K : RelativeDiagram.Rooted.DMod D.algebraCocone.pt}
    (hK : @DerivedCategory.IsPerfectOver D.baseCocone.pt inferInstance
      D.algebraCocone.pt inferInstance D.targetAlg K) =>
  (S.exists_stage_of_isPerfectOver hbase halgebra hflat hfp hK :
    ∃ (i : I) (Ki : RelativeDiagram.Rooted.DMod (D.algebra.obj i)),
      @DerivedCategory.IsPerfectOver (D.base.obj i) inferInstance
          (D.algebra.obj i) inferInstance (D.relativeAlg i) Ki ∧
        IsIsomorphic K ((D.extend i).obj Ki))

/- Lemma 15.85.7 (Stacks `0DHX`) (2): the canonical stage Hom maps form the target Hom colimit. -/
@[stacks 0DHX "filtered Hom comparison for scalar extension"]
#check fun {I : Type v} [Category.{w} I]
    {D : RelativeDiagram.{u, v, w} (I := I)} (S : D.Rooted) [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone) (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin))
    (K₀ L₀ : RelativeDiagram.Rooted.source S) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ : @DerivedCategory.HasFiniteTorDimensionOver
      (D.base.obj S.origin) inferInstance (D.algebra.obj S.origin) inferInstance
        (D.relativeAlg S.origin) L₀) =>
  (S.homDiagram_isColimit_exists hbase halgebra hflat hfp K₀ L₀ hK₀ hL₀ :
    S.HomColimit K₀ L₀)
#check @RelativeDiagram.Rooted.hom_factor
#check @RelativeDiagram.Rooted.hom_eventually_eq

/- Lemma 15.85.7 (Stacks `0DHX`), category-colimit consequence: object descent and the canonical
Hom colimits give the operational filtered-colimit criterion for relative-perfect categories. -/
@[stacks 0DHX "relative-perfect category colimit"]
#check fun {I : Type v} [Category.{w} I]
    {D : RelativeDiagram.{u, v, w} (I := I)} (S : D.Rooted) [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone) (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin)) =>
  (S.isRelativePerfectCategoryColimit hbase halgebra hflat hfp :
    S.IsRelativePerfectCategoryColimit)

#check @RelativeDiagram.Rooted.IsRelativePerfectCategoryColimit
#check @RelativeDiagram.Rooted.IsRelativePerfectCategoryColimit.spec
