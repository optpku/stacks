module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Exactness
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.IdealPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Ideal-power torsion and coherent completion

Coherent formal modules uniformly annihilated by an ideal power are algebraizable. Completion is
fully faithful on Hom and degree-one Ext when either endpoint is uniformly ideal-power torsion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module is uniformly annihilated on affine opens by a power of an ideal
sheaf when one positive exponent annihilates every stage on every affine open. -/
@[stacks 0EHP "uniform ideal-power torsion for coherent formal modules"]
def IsAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} (I : X.IdealSheafData) (E : CoherentFormalModules X I) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, ∀ U : X.affineOpens,
    I.ideal U ^ c •
        (⊤ : Submodule Γ(X, U.1) (((E.obj).obj (op n)).obj.val.obj (op U.1))) = ⊥

/-- Uniform ideal-power annihilation of a coherent formal module unfolds to one positive
exponent annihilating every affine-open section module at every stage. -/
theorem isAnnihilatedByIdealPowerOnAffineOpens_iff
    {X : Scheme.{u}} (I : X.IdealSheafData) (E : CoherentFormalModules X I) :
    IsAnnihilatedByIdealPowerOnAffineOpens I E ↔
      ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, ∀ U : X.affineOpens,
        I.ideal U ^ c •
            (⊤ : Submodule Γ(X, U.1) (((E.obj).obj (op n)).obj.val.obj (op U.1))) = ⊥ :=
  sorry

/-- A coherent formal module uniformly annihilated by a positive ideal power lies in the
essential image of coherent completion. -/
theorem mem_completion_essImage_of_isAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I) (E : CoherentFormalModules X I)
    (hE : IsAnnihilatedByIdealPowerOnAffineOpens I E) :
    ctx.toFunctor.essImage E := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules

namespace CoherentCompletionFunctor

/-- Completion induces a bijection on morphisms when either coherent module is uniformly
annihilated on affine opens by an ideal power. -/
theorem homMap_bijective_of_isAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace)
    (hFG : Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
      Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) :
    Function.Bijective (fun f : F ⟶ G ↦ ctx.toFunctor.map f) := sorry

/-- The concrete degree-one Ext map induced by a coherent-completion presentation. Exactness
and additivity are derived from the presentation only while the map is constructed. -/
@[stacks 0EHP "degree-one Ext map for a completion presentation"]
noncomputable def extOneMap
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    [HasExt (RingedSpace.Coh X.toRingedSpace)]
    [HasExt (Scheme.CoherentFormalModules X I)]
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace) :
    Ext F G 1 →+ Ext (ctx.obj F) (ctx.obj G) 1 :=
  let sourceAbelian : Abelian (RingedSpace.Coh X.toRingedSpace) := inferInstance
  let targetAbelian : Abelian (Scheme.CoherentFormalModules X I) := inferInstance
  -- Local instance justification (defeq pin): pin the source Abelian structure's Preadditive
  -- projection only while constructing the exact Ext map.
  letI : Preadditive (RingedSpace.Coh X.toRingedSpace) :=
    sourceAbelian.toPreadditive
  -- Local instance justification (defeq pin): pin the target Abelian structure's Preadditive
  -- projection only while constructing the exact Ext map.
  letI : Preadditive (Scheme.CoherentFormalModules X I) :=
    targetAbelian.toPreadditive
  -- Local instance justification (search instability): derive finite-limit preservation for
  -- this explicit presentation only while `mapExtAddHom` is constructed.
  letI : PreservesFiniteLimits ctx.toFunctor :=
    (coherentCompletionFunctor_exact ctx).1
  -- Local instance justification (search instability): derive finite-colimit preservation for
  -- this explicit presentation only while `mapExtAddHom` is constructed.
  letI : PreservesFiniteColimits ctx.toFunctor :=
    (coherentCompletionFunctor_exact ctx).2
  -- Local instance justification (search instability): derive additivity for this explicit
  -- presentation only while `mapExtAddHom` is constructed.
  letI : ctx.toFunctor.Additive :=
    exactFunctor_le_additiveFunctor _ _ ctx.toFunctor (coherentCompletionFunctor_exact ctx)
  ctx.toFunctor.mapExtAddHom F G 1

/-- Completion induces a bijection on degree-one Ext when either coherent module is uniformly
annihilated on affine opens by an ideal power. -/
theorem extOneMap_bijective_of_isAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    [HasExt (RingedSpace.Coh X.toRingedSpace)]
    [HasExt (Scheme.CoherentFormalModules X I)]
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace)
    (hFG : Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
      Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) :
    Function.Bijective (extOneMap ctx F G) := sorry

end CoherentCompletionFunctor

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- Lemma 30.23.7 (0EHP) (1): a coherent formal module uniformly annihilated by a positive
ideal power lies in the essential image of the canonical completion functor. -/
@[stacks 0EHP "ideal-power torsion lies in the canonical completion image"]
theorem mem_essImage_of_isAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (E : CoherentFormalModules X I)
    (hE : CoherentFormalModules.IsAnnihilatedByIdealPowerOnAffineOpens I E) :
    (functor I).essImage E := sorry

/-- Lemma 30.23.7 (0EHP) (2): canonical completion induces a bijection on morphisms when either
coherent module is uniformly annihilated on affine opens by an ideal power. -/
@[stacks 0EHP "Hom comparison for ideal-power torsion"]
theorem homMap_bijective_of_isAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (F G : RingedSpace.Coh X.toRingedSpace)
    (hFG : Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
      Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) :
    Function.Bijective (fun f : F ⟶ G ↦ (functor I).map f) := sorry
/-- The concrete degree-one Ext map induced by canonical completion. The internal instance
pins are encapsulated by the reusable presentation-level map. -/
@[stacks 0EHP "canonical degree-one Ext map"]
noncomputable def extOneMap
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    [HasExt (RingedSpace.Coh X.toRingedSpace)]
    [HasExt (CoherentFormalModules X I)]
    (F G : RingedSpace.Coh X.toRingedSpace) :
    Ext F G 1 →+ Ext ((functor I).obj F) ((functor I).obj G) 1 :=
  CoherentCompletionFunctor.extOneMap
    (CoherentCompletionFunctor.canonical X I) F G

/-- Lemma 30.23.7 (0EHP) (3): canonical completion induces a bijection on degree-one Ext when
either coherent module is uniformly annihilated on affine opens by an ideal power. -/
@[stacks 0EHP "Ext comparison for ideal-power torsion"]
theorem extOneMap_bijective_of_isAnnihilatedByIdealPowerOnAffineOpens
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    [HasExt (RingedSpace.Coh X.toRingedSpace)]
    [HasExt (CoherentFormalModules X I)]
    (F G : RingedSpace.Coh X.toRingedSpace)
    (hFG : Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
      Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) :
    Function.Bijective (extOneMap (I := I) F G) := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
