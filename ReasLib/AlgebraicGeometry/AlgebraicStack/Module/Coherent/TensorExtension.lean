/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Extension of right exact tensor functors from coherent modules

The extension preserves all colimits of the ambient module universe. The natural
abstract generalization is extension from finitely presentable filtered
generators with tensor products commuting with colimits; the geometric
statements here impose no extra smallness hypotheses on coherent modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The coherent inclusion inherits the canonical monoidal structure of the
inclusion between full monoidal subcategories of fppf modules. -/
instance Coh.toQCoh_monoidal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    (Coh.toQCoh : Coh X ⥤ QCoh X).Monoidal := by
  let h : coherentModuleProperty X ≤ quasiCoherentModuleProperty X := fun M hM ↦ by
    rcases hM.toIsFinitePresentation with ⟨⟨q, _⟩⟩
    exact q.isQuasicoherent
  change (ObjectProperty.ιOfLE h).Monoidal
  infer_instance

/-- The coherent inclusion preserves the inherited symmetry. -/
instance Coh.toQCoh_braided {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    (Coh.toQCoh : Coh X ⥤ QCoh X).Braided := by
  let h : coherentModuleProperty X ≤ quasiCoherentModuleProperty X := fun M hM ↦ by
    rcases hM.toIsFinitePresentation with ⟨⟨q, _⟩⟩
    exact q.isQuasicoherent
  change (ObjectProperty.ιOfLE h).Braided
  infer_instance

/-- A right exact symmetric tensor functor on coherent modules of Noetherian
algebraic stacks extends to a symmetric monoidal functor preserving all colimits.
The restriction isomorphism respects both the unit and the tensor constraints. -/
theorem exists_extend_rightExactTensor
    {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [F.Braided] [PreservesFiniteColimits F] :
    ∃ (G : QCoh X ⥤ QCoh Y) (m : G.Braided),
      letI := m;
      PreservesColimitsOfSize.{u, u} G ∧
        ∃ e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
            F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y),
          NatTrans.IsMonoidal e.hom :=
  sorry

/-- Two filtered-colimit-preserving monoidal extensions with specified monoidal
restriction isomorphisms have a unique monoidal comparison inducing those
isomorphisms. No braiding assumption is needed for this uniqueness statement. -/
theorem extend_rightExactTensor_unique
    {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [F.Monoidal]
    (G G' : QCoh X ⥤ QCoh Y) [G.Monoidal] [G'.Monoidal]
    (hG : PreservesFilteredColimitsOfSize.{u, u} G)
    (hG' : PreservesFilteredColimitsOfSize.{u, u} G')
    (e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
      F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y))
    (e' : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G' ≅
      F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y))
    [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal e'.hom] :
    ∃! t : G ≅ G', NatTrans.IsMonoidal t.hom ∧
      Functor.isoWhiskerLeft (Coh.toQCoh : Coh X ⥤ QCoh X) t ≪≫ e' = e :=
  sorry

/-- A right exact symmetric tensor functor between coherent modules of
Noetherian algebraic stacks extends to a colimit-preserving symmetric monoidal
functor. Among filtered-colimit-preserving monoidal extensions, the comparison
respecting the specified monoidal restriction isomorphisms exists uniquely. -/
theorem existsUnique_extend_rightExactTensor
    {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [F.Braided] [PreservesFiniteColimits F] :
    ∃ (G : QCoh X ⥤ QCoh Y) (m : G.Braided),
      letI := m;
      PreservesColimitsOfSize.{u, u} G ∧
        ∃ e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
            F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y),
          NatTrans.IsMonoidal e.hom ∧
          ∀ (G' : QCoh X ⥤ QCoh Y) [G'.Monoidal],
            PreservesFilteredColimitsOfSize.{u, u} G' →
            ∀ e' : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G' ≅
                F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y),
              NatTrans.IsMonoidal e'.hom →
              ∃! t : G ≅ G', NatTrans.IsMonoidal t.hom ∧
                Functor.isoWhiskerLeft (Coh.toQCoh : Coh X ⥤ QCoh X) t ≪≫ e' = e := by
  obtain ⟨G, m, hG, e, he⟩ := exists_extend_rightExactTensor F
  letI := m
  letI := hG
  letI := he
  refine ⟨G, m, hG, e, he, ?_⟩
  intro G' m' hG' e' he'
  letI := he'
  exact extend_rightExactTensor_unique F G G' (by infer_instance) hG' e e'

end AlgebraicGeometry.AlgebraicStack
