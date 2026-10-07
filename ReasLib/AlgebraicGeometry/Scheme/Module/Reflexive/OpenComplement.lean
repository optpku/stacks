module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Pullback

/-!
# Coherent reflexive modules across an open complement

Pullback and pushforward along an open immersion induce an equivalence on coherent reflexive
module sheaves when the local rings off the open subscheme have depth at least two.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (U : X.Opens)

/-- Pullback to an open subscheme preserves reflexivity for coherent reflexive modules under the
depth-at-least-two hypothesis on the complement. -/
theorem reflexiveCohOpenPullback_obj_isReflexive
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (ℱ : ReflexiveCoh X) :
    IsReflexive
      ((Scheme.Modules.pullback U.ι).obj ((reflexiveCohForget X).obj ℱ)) := sorry

/-- The canonical pullback to an open subscheme, restricted to coherent reflexive modules. -/
noncomputable def reflexiveCohOpenPullback
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    ReflexiveCoh X ⥤ ReflexiveCoh (U : Scheme) :=
  ObjectProperty.lift (reflexiveCohProperty (U : Scheme))
    (ObjectProperty.lift (SheafOfModules.isCoherent (U : Scheme).ringCatSheaf)
      (reflexiveCohForget X ⋙ Scheme.Modules.pullback U.ι)
      (fun ℱ ↦
        @pullback_isCoherent (U : Scheme) X inferInstance inferInstance U.ι
          ((reflexiveCohForget X).obj ℱ) ℱ.obj.property))
    (reflexiveCohOpenPullback_obj_isReflexive U hdepth)

/-- Pushforward from an open subscheme preserves coherence for coherent reflexive modules under
the depth-at-least-two hypothesis on the complement. -/
theorem reflexiveCohOpenPushforward_obj_isCoherent
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (𝒢 : ReflexiveCoh (U : Scheme)) :
    ((Scheme.Modules.pushforward U.ι).obj
      ((reflexiveCohForget (U : Scheme)).obj 𝒢)).IsCoherent := sorry

/-- Pushforward from an open subscheme preserves reflexivity for coherent reflexive modules under
the depth-at-least-two hypothesis on the complement. -/
theorem reflexiveCohOpenPushforward_obj_isReflexive
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (𝒢 : ReflexiveCoh (U : Scheme)) :
    IsReflexive
      ((Scheme.Modules.pushforward U.ι).obj
        ((reflexiveCohForget (U : Scheme)).obj 𝒢)) := sorry

/-- The canonical pushforward from an open subscheme, restricted to coherent reflexive modules. -/
noncomputable def reflexiveCohOpenPushforward
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    ReflexiveCoh (U : Scheme) ⥤ ReflexiveCoh X :=
  ObjectProperty.lift (reflexiveCohProperty X)
    (ObjectProperty.lift (SheafOfModules.isCoherent X.ringCatSheaf)
      (reflexiveCohForget (U : Scheme) ⋙ Scheme.Modules.pushforward U.ι)
      (reflexiveCohOpenPushforward_obj_isCoherent U hdepth))
    (reflexiveCohOpenPushforward_obj_isReflexive U hdepth)

/-- Forgetting the restricted open pullback recovers the ambient pullback functor. -/
noncomputable def reflexiveCohOpenPullbackCompForgetIso
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    reflexiveCohOpenPullback U hdepth ⋙ reflexiveCohForget (U : Scheme) ≅
      reflexiveCohForget X ⋙ Scheme.Modules.pullback U.ι :=
  Iso.refl _

/-- Forgetting the restricted open pushforward recovers the ambient pushforward functor. -/
noncomputable def reflexiveCohOpenPushforwardCompForgetIso
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    reflexiveCohOpenPushforward U hdepth ⋙ reflexiveCohForget X ≅
      reflexiveCohForget (U : Scheme) ⋙ Scheme.Modules.pushforward U.ι :=
  Iso.refl _

/-- The pullback-pushforward adjunction restricted to coherent reflexive modules across an open
complement of local-ring depth at least two. -/
noncomputable def reflexiveCohOpenAdjunction
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    reflexiveCohOpenPullback U hdepth ⊣ reflexiveCohOpenPushforward U hdepth :=
  (Scheme.Modules.pullbackPushforwardAdjunction U.ι).restrictFullyFaithful
    ((reflexiveCohProperty X).fullyFaithfulι.comp
      (SheafOfModules.isCoherent X.ringCatSheaf).fullyFaithfulι)
    ((reflexiveCohProperty (U : Scheme)).fullyFaithfulι.comp
      (SheafOfModules.isCoherent (U : Scheme).ringCatSheaf).fullyFaithfulι)
    (reflexiveCohOpenPullbackCompForgetIso U hdepth).symm
    (reflexiveCohOpenPushforwardCompForgetIso U hdepth).symm

/-- The unit of the restricted open pullback-pushforward adjunction is invertible. -/
theorem isIso_reflexiveCohOpenAdjunction_unit_app
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (ℱ : ReflexiveCoh X) :
    IsIso ((reflexiveCohOpenAdjunction U hdepth).unit.app ℱ) := sorry

/-- The restricted open pullback-pushforward adjunction has an invertible unit at every coherent
reflexive module. -/
instance instIsIsoReflexiveCohOpenAdjunctionUnitApp
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (ℱ : ReflexiveCoh X) :
    IsIso ((reflexiveCohOpenAdjunction U hdepth).unit.app ℱ) :=
  isIso_reflexiveCohOpenAdjunction_unit_app U hdepth ℱ

/-- The counit of the restricted open pullback-pushforward adjunction is invertible. -/
theorem isIso_reflexiveCohOpenAdjunction_counit_app
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (𝒢 : ReflexiveCoh (U : Scheme)) :
    IsIso ((reflexiveCohOpenAdjunction U hdepth).counit.app 𝒢) := sorry

/-- The restricted open pullback-pushforward adjunction has an invertible counit at every coherent
reflexive module. -/
instance instIsIsoReflexiveCohOpenAdjunctionCounitApp
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z))
    (𝒢 : ReflexiveCoh (U : Scheme)) :
    IsIso ((reflexiveCohOpenAdjunction U hdepth).counit.app 𝒢) :=
  isIso_reflexiveCohOpenAdjunction_counit_app U hdepth 𝒢

/-- Coherent reflexive modules on an integral locally Noetherian scheme are equivalent to those
on an open subscheme when the local rings off the open have depth at least two. -/
noncomputable def reflexiveCohOpenEquivalence
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    ReflexiveCoh X ≌ ReflexiveCoh (U : Scheme) :=
  (reflexiveCohOpenAdjunction U hdepth).toEquivalence

/-- The forward functor of the coherent-reflexive open-complement equivalence is the canonical
restricted pullback. -/
@[simp]
theorem reflexiveCohOpenEquivalence_functor
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    (reflexiveCohOpenEquivalence U hdepth).functor = reflexiveCohOpenPullback U hdepth := rfl

/-- The inverse functor of the coherent-reflexive open-complement equivalence is the canonical
restricted pushforward. -/
@[simp]
theorem reflexiveCohOpenEquivalence_inverse
    (hdepth : ∀ z : X, z ∉ U →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)) :
    (reflexiveCohOpenEquivalence U hdepth).inverse =
      reflexiveCohOpenPushforward U hdepth := rfl

end AlgebraicGeometry.Scheme.Modules
