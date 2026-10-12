/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sets.Compacts
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Hom
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

/-!
# Neighborhood completion

This file constructs the comparison from sections on open neighborhoods of a closed
subscheme to sections on its infinitesimal neighborhoods.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] AlgebraicGeometry.Scheme.Opens.toScheme

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The support of ideal-sheaf data, regarded as a compact subset of a Noetherian scheme. -/
def compactSupport (I : X.IdealSheafData) : Compacts X :=
  ⟨(I.support : Set X), NoetherianSpace.isCompact _⟩

/-- The compact set underlying `compactSupport I` is the support of `I`. -/
theorem coe_compactSupport (I : X.IdealSheafData) :
    (compactSupport I : Set X) = I.support := sorry

/-- The diagram of sections of `M` over the open neighborhoods of the closed support of `I`,
ordered by reverse inclusion. -/
abbrev neighborhoodSectionsDiagram (I : X.IdealSheafData) (M : X.Modules) :
    (compactSupport I).openNhdsᵒᵖ ⥤ Type u :=
  (OrderHom.Subtype.val (compactSupport I).openNhds).toFunctor.op ⋙
    M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat

/-- At an open neighborhood `V`, the neighborhood section diagram has the sections of `M`
over `V` as its value. -/
theorem neighborhoodSectionsDiagram_obj (I : X.IdealSheafData) (M : X.Modules)
    (V : (compactSupport I).openNhdsᵒᵖ) :
    (neighborhoodSectionsDiagram I M).obj V = M.val.obj (op V.unop.val) := sorry

/-- At ideal power `n`, the diagram of sections of `M / I ^ n M` over all open neighborhoods
of the support of `I`. -/
abbrev neighborhoodQuotientSectionsDiagram (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (compactSupport I).openNhdsᵒᵖ ⥤ Type u :=
  (OrderHom.Subtype.val (compactSupport I).openNhds).toFunctor.op ⋙
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      I.toSubobject M n).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat

/-- Quotient projection on neighborhood sections commutes with restriction of sections. -/
theorem neighborhoodQuotientProjection_naturality
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ)
    {V W : (compactSupport I).openNhdsᵒᵖ} (f : V ⟶ W) :
    (neighborhoodSectionsDiagram I M).map f ≫
        ↾((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.projection.{u, u, u}
          I.toSubobject M n).val.app (op W.unop.val)) =
      ↾((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.projection.{u, u, u}
          I.toSubobject M n).val.app (op V.unop.val)) ≫
        (neighborhoodQuotientSectionsDiagram I M n).map f := sorry

/-- The canonical natural transformation on neighborhood sections induced by
`M ⟶ M / I ^ n M`. -/
def neighborhoodQuotientProjection (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    neighborhoodSectionsDiagram I M ⟶ neighborhoodQuotientSectionsDiagram I M n where
  app V :=
    ↾((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.projection.{u, u, u}
      I.toSubobject M n).val.app (op V.unop.val))
  naturality _ _ f := neighborhoodQuotientProjection_naturality I M n f

/-- The ideal-power transition on neighborhood sections commutes with restriction. -/
theorem neighborhoodQuotientTransition_naturality
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ)
    {V W : (compactSupport I).openNhdsᵒᵖ} (f : V ⟶ W) :
    (neighborhoodQuotientSectionsDiagram I M (n + 1)).map f ≫
        ↾((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.step.{u, u, u}
          I.toSubobject M n).val.app (op W.unop.val)) =
      ↾((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.step.{u, u, u}
          I.toSubobject M n).val.app (op V.unop.val)) ≫
        (neighborhoodQuotientSectionsDiagram I M n).map f := sorry

/-- The natural transformation on neighborhood quotient sections induced by
`M / I ^ (n + 1) M ⟶ M / I ^ n M`. -/
def neighborhoodQuotientTransition (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    neighborhoodQuotientSectionsDiagram I M (n + 1) ⟶
      neighborhoodQuotientSectionsDiagram I M n where
  app V :=
    ↾((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.step.{u, u, u}
      I.toSubobject M n).val.app (op V.unop.val))
  naturality _ _ f := neighborhoodQuotientTransition_naturality I M n f

/-- The transition between neighborhood colimits of consecutive ideal-power quotients. -/
noncomputable def neighborhoodQuotientColimitStep
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    colimit (neighborhoodQuotientSectionsDiagram I M (n + 1)) ⟶
      colimit (neighborhoodQuotientSectionsDiagram I M n) :=
  colim.map (neighborhoodQuotientTransition I M n)

/-- The positive ideal-power inverse system whose stage `n` is the colimit, over open
neighborhoods, of sections of `M / I ^ (n + 1) M`. -/
noncomputable def positiveNeighborhoodSectionsSystem
    (I : X.IdealSheafData) (M : X.Modules) : SequentialInverseSystem (Type u) :=
  @Functor.ofOpSequence (Type u) inferInstance
    (fun n ↦ colimit (neighborhoodQuotientSectionsDiagram I M (n + 1)))
    (fun n ↦ neighborhoodQuotientColimitStep I M (n + 1))

/-- The quotient projections induce the canonical map from the neighborhood colimit of
sections of `M` to stage `n` of the positive neighborhood-completion system. -/
noncomputable def neighborhoodSectionsProjection
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (colimit (neighborhoodSectionsDiagram I M))).obj (op n) ⟶
      (positiveNeighborhoodSectionsSystem I M).obj (op n) :=
  colim.map (neighborhoodQuotientProjection I M (n + 1))

/-- The canonical neighborhood section projections commute with ideal-power transitions. -/
theorem neighborhoodSectionsProjection_naturality
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (colimit (neighborhoodSectionsDiagram I M))).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ neighborhoodSectionsProjection I M n =
      neighborhoodSectionsProjection I M (n + 1) ≫
        (positiveNeighborhoodSectionsSystem I M).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from the neighborhood colimit of sections to the positive
neighborhood-completion system. -/
noncomputable def neighborhoodSectionsCone
    (I : X.IdealSheafData) (M : X.Modules) :
    Cone (positiveNeighborhoodSectionsSystem I M) where
  pt := colimit (neighborhoodSectionsDiagram I M)
  π := NatTrans.ofOpSequence (neighborhoodSectionsProjection I M)
    (neighborhoodSectionsProjection_naturality I M)

/-- The canonical comparison from the colimit of sections over open neighborhoods to the
inverse limit of sections on the infinitesimal neighborhoods. -/
noncomputable def neighborhoodComparison (I : X.IdealSheafData) (M : X.Modules) :
    colimit (neighborhoodSectionsDiagram I M) ⟶
      limit (positiveNeighborhoodSectionsSystem I M) :=
  limit.lift (positiveNeighborhoodSectionsSystem I M) (neighborhoodSectionsCone I M)

/-- Every limit projection of `neighborhoodComparison I M` is induced by restriction of
sections followed by the corresponding ideal-power quotient projection. -/
theorem neighborhoodComparison_fac (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    neighborhoodComparison I M ≫
        limit.π (positiveNeighborhoodSectionsSystem I M) (op n) =
      neighborhoodSectionsProjection I M n := sorry

/-- The internal-Hom comparison maps are bijective for all finite locally free objects on
open neighborhoods of the support of `I`. -/
def NeighborhoodCompletionFullyFaithful (I : X.IdealSheafData) : Prop :=
  ∀ (V : (compactSupport I).openNhds)
    (E F : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
      finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) F →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens)))
            (Scheme.Modules.internalHom E.obj F.obj))

/-- Full faithfulness of neighborhood completion is equivalent to bijectivity of all canonical
internal-Hom comparison maps on finite locally free objects. -/
theorem neighborhoodCompletionFullyFaithful_iff (I : X.IdealSheafData) :
    NeighborhoodCompletionFullyFaithful I ↔
      ∀ (V : (compactSupport I).openNhds)
        (E F : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
          finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
            finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) F →
              Function.Bijective (neighborhoodComparison
                (I.comap (Scheme.Opens.ι (V.val : X.Opens)))
                (Scheme.Modules.internalHom E.obj F.obj)) := sorry

/-- Quasi-affineness and bijectivity for the structure sheaf imply eventual bijectivity for
tensor powers of an ample module in the neighborhood comparison. -/
theorem quasiAffine_implies_hasAmple_neighborhoodCompletion
    (I : X.IdealSheafData)
    (hX : X.IsQuasiAffine)
    (h_complete : Function.Bijective
      (neighborhoodComparison I (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ L : X.Modules, Modules.isAmpleObject L ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀,
        Function.Bijective
          (neighborhoodComparison I (RingedSpace.TensorPower.sheaf L m)) := sorry

/-- Eventual bijectivity for ample tensor powers implies bijectivity for every finite locally
free module on every open neighborhood of the support. -/
theorem hasAmple_implies_finiteLocallyFree_neighborhoodCompletion
    (I : X.IdealSheafData) (L : X.Modules)
    (hL : Modules.isAmpleObject L)
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (neighborhoodComparison I (RingedSpace.TensorPower.sheaf L m))) :
    ∀ (V : (compactSupport I).openNhds)
      (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj) := sorry

/-- Bijectivity for every finite locally free module implies full faithfulness of neighborhood
completion on finite locally free objects. -/
theorem finiteLocallyFree_implies_fullyFaithful_neighborhoodCompletion
    (I : X.IdealSheafData)
    (h_complete : ∀ (V : (compactSupport I).openNhds)
      (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj)) :
    NeighborhoodCompletionFullyFaithful I := sorry

/-- Full faithfulness of neighborhood completion implies bijectivity for every finite locally
free module on every open neighborhood of the support. -/
theorem fullyFaithful_implies_finiteLocallyFree_neighborhoodCompletion
    (I : X.IdealSheafData)
    (h_fully_faithful : NeighborhoodCompletionFullyFaithful I) :
    ∀ (V : (compactSupport I).openNhds)
      (E : RingedSpace.Coh (Scheme.Opens.toScheme (V.val : X.Opens)).toRingedSpace),
        finiteLocallyFree (Scheme.Opens.toScheme (V.val : X.Opens)) E →
          Function.Bijective (neighborhoodComparison
            (I.comap (Scheme.Opens.ι (V.val : X.Opens))) E.obj) := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
