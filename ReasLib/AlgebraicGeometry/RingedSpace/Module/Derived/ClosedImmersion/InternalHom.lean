/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded

@[expose] public section

/-!
# Derived internal Hom for a closed immersion

This module compares the derived pushforward of internal Hom from the structure sheaf with
the ambient derived internal-Hom construction.
-/

open CategoryTheory
open AlgebraicGeometry
open scoped CartesianClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

/-- The K-injective total right-derived internal Hom from the structure sheaf of the source of a
closed immersion. -/
noncomputable def rHomFromStructureSheaf
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    RingedSpace.ModuleDerived X ⥤ RingedSpace.ModuleDerived Z :=
  -- Local instance justification (proof-local temporary data): the additive structure is used only to form the K-injective right-derived functor of this explicit right adjoint.
  letI : (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
      i h_closed).Additive :=
    (RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction
      i h_closed).right_adjoint_additive
  Adjunction.Derived.KInjective.right
    (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
      i h_closed)

/-- The K-injective derived internal Hom from the source structure sheaf, followed by derived
pushforward along a closed immersion. -/
noncomputable def pushforwardRHomStructureSheaf
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    RingedSpace.ModuleDerived X ⥤ RingedSpace.ModuleDerived X :=
  -- Local instance justification (proof-local temporary data): the additive structure is used only to form the K-injective right-derived functor of this explicit right adjoint.
  letI : (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
      i h_closed).Additive :=
    (RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction
      i h_closed).right_adjoint_additive
  Adjunction.Derived.KInjective.right
      (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
        i h_closed) ⋙
    RingedSpace.moduleDerivedPushforward i

/-- The K-injective right-derived ambient internal Hom from the pushed-forward structure sheaf
of the source of a closed immersion. -/
noncomputable def ambientRHomStructureSheaf
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    RingedSpace.ModuleDerived X ⥤ RingedSpace.ModuleDerived X :=
  -- Local instance justification (proof-local temporary data): this additive structure transports along the underived closed-immersion adjunction only while deriving the ambient internal-Hom functor.
  letI : (RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
      i h_closed).Additive :=
    (RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction
      i h_closed).right_adjoint_additive
  -- Local instance justification (proof-local temporary data): the underived comparison supplies additivity of the ambient functor only for its K-injective derivation.
  letI : (RingedSpace.Hom.ModulePushforward.ClosedImmersion.ambientInternalHom i).Additive :=
    Functor.additive_of_iso
      (RingedSpace.Hom.ModulePushforward.ClosedImmersion.pushforwardHomFromStructureSheafIso
        i h_closed)
  Adjunction.Derived.KInjective.right
    (RingedSpace.Hom.ModulePushforward.ClosedImmersion.ambientInternalHom i)

/-- Derived pushforward of internal Hom from the source structure sheaf is objectwise
isomorphic to the ambient derived internal Hom from its direct image. -/
theorem pushforwardRHomStructureSheaf_isomorphic
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (K : RingedSpace.ModuleDerived X) :
    IsIsomorphic
      ((pushforwardRHomStructureSheaf i h_closed).obj K)
      ((ambientRHomStructureSheaf i h_closed).obj K) := sorry

/-- The derived internal Hom from a pushed-forward object is isomorphic to the derived pushforward
of the internal Hom into the canonical derived Hom from the structure sheaf. -/
theorem pushforward_internalHom_isomorphic
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    [MonoidalCategory (RingedSpace.ModuleDerived X)]
    [MonoidalClosed (RingedSpace.ModuleDerived X)]
    [MonoidalCategory (RingedSpace.ModuleDerived Z)]
    [MonoidalClosed (RingedSpace.ModuleDerived Z)]
    (M : RingedSpace.ModuleDerived Z) (K : RingedSpace.ModuleDerived X) :
    IsIsomorphic
      (((RingedSpace.moduleDerivedPushforward i).obj M) ⟹ K)
      ((RingedSpace.moduleDerivedPushforward i).obj
        (M ⟹ (rHomFromStructureSheaf i h_closed).obj K)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion
