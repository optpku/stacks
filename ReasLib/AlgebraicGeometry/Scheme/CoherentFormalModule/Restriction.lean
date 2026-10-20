module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Topology.Sets.OpenCover
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Restriction of coherent formal modules

This file defines stagewise restriction of coherent formal module systems, proves that it is
exact, and characterizes exactness locally on an open cover.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- Stagewise restriction along an open subscheme preserves the coherent-formal-system
conditions. -/
theorem isCoherentFormalModuleSystem_restrict {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens)
    (F : SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace))
    (hF : IsCoherentFormalModuleSystem I F) :
    IsCoherentFormalModuleSystem
      (I.comap (X.ofRestrict U.isOpenEmbedding))
      (F ⋙ Modules.coherentRestrictFunctor (X.ofRestrict U.isOpenEmbedding)) := sorry

/-- The canonical functor restricting a coherent formal module system stagewise to an open
subscheme. -/
noncomputable def coherentFormalModulesRestrictionFunctor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.Opens) :
    CoherentFormalModules X I ⥤
      CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding)) :=
  (IsCoherentFormalModuleSystem
      (I.comap (X.ofRestrict U.isOpenEmbedding))).lift
    ((IsCoherentFormalModuleSystem I).ι ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (RingedSpace.Coh X.toRingedSpace)
        (RingedSpace.Coh (X.restrict U.isOpenEmbedding).toRingedSpace)).obj
          (Modules.coherentRestrictFunctor (X.ofRestrict U.isOpenEmbedding)))
    (fun F ↦ isCoherentFormalModuleSystem_restrict I U F.obj F.property)

namespace CoherentFormalModules

/-- A coherent formal module on an open subscheme extends to the ambient scheme when it lies in
the essential image of the coherent-formal restriction functor. -/
def extendsTo {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens)
    (F : CoherentFormalModules (X.restrict U.isOpenEmbedding)
      (I.comap (X.ofRestrict U.isOpenEmbedding))) : Prop :=
  (coherentFormalModulesRestrictionFunctor I U).essImage F

end CoherentFormalModules

/-- The canonical coherent-formal restriction functor restricts every stage and every stagewise
morphism by the ordinary module restriction functor. -/
theorem coherentFormalModulesRestrictionFunctor_spec {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.Opens) :
    (∀ (M : CoherentFormalModules X I) (n : ℕ),
      ((((coherentFormalModulesRestrictionFunctor I U).obj M).obj).obj (op n)).obj =
        (Modules.restrictFunctor (X.ofRestrict U.isOpenEmbedding)).obj
          (((M.obj).obj (op n)).obj)) ∧
      ∀ {M N : CoherentFormalModules X I} (f : M ⟶ N) (n : ℕ),
        (((coherentFormalModulesRestrictionFunctor I U).map f).hom.app (op n)).hom =
          (Modules.restrictFunctor (X.ofRestrict U.isOpenEmbedding)).map
            ((f.hom.app (op n)).hom) := sorry

/-- The canonical restriction functor on coherent formal modules over a Noetherian scheme is
exact. -/
theorem coherentFormalModulesRestrictionFunctor_exact {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens) :
    exactFunctor (CoherentFormalModules X I)
      (CoherentFormalModules (X.restrict U.isOpenEmbedding)
        (I.comap (X.ofRestrict U.isOpenEmbedding)))
      (coherentFormalModulesRestrictionFunctor I U) := sorry

/-- The canonical coherent-formal restriction functor preserves finite limits. -/
instance coherentFormalModulesRestrictionFunctor_preservesFiniteLimits
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens) :
    PreservesFiniteLimits (coherentFormalModulesRestrictionFunctor I U) :=
  (coherentFormalModulesRestrictionFunctor_exact I U).1

/-- The canonical coherent-formal restriction functor preserves finite colimits. -/
instance coherentFormalModulesRestrictionFunctor_preservesFiniteColimits
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens) :
    PreservesFiniteColimits (coherentFormalModulesRestrictionFunctor I U) :=
  (coherentFormalModulesRestrictionFunctor_exact I U).2

/-- Exactness of a short complex of coherent formal modules can be checked after restriction to
every member of an open cover. -/
theorem coherentFormalModules_exact_iff_of_openCover {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    {ι : Type v} (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (S : ShortComplex (CoherentFormalModules X I)) :
    S.Exact ↔
      ∀ i : ι, (S.map (coherentFormalModulesRestrictionFunctor I (U i))).Exact := sorry

end AlgebraicGeometry.Scheme
