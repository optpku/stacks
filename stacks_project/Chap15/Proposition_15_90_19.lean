module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single.Finite
import StacksCheckRecall

/-!
# Proposition 15.90.19

Finitely generated modules over a Noetherian ring satisfy formal gluing for
the completion at a principal ideal.

@stack 05ET
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} [CommRing R] (f : R)

-- These shorthands display the source's completion-localization pullback and
-- introduce no local instances or data.
local notation "RHat" => principalAdicCompletion f
local notation "RHatf" => Localization.Away (algebraMap R RHat f)
local notation "Rf" => Localization.Away f
local notation "completionOverlapFG" =>
  FGModuleCat.extendScalars (algebraMap RHat RHatf)
local notation "localizationOverlapFG" =>
  FGModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f)
local notation "FGGlueCat" =>
  CategoricalPullback completionOverlapFG localizationOverlapFG

/- The object assignment records the completed module, its localization away
from `f`, and their canonical identification over the overlap. -/
@[stacks 05ET "finite principal-adic formal-gluing object"]
#check (principalAdicFormalGlueingFGObj f : FGModuleCat.{u} R → FGGlueCat)

/- The object and morphism assignments form the displayed finite-module
formal-gluing functor. -/
@[stacks 05ET "finite principal-adic formal-gluing functor"]
#check (principalAdicFormalGlueingFGFunctor f :
  FGModuleCat.{u} R ⥤ FGGlueCat)

variable [IsNoetherianRing R]

/- Proposition 15.90.19 (05ET): the finite-module formal-gluing functor for
the `f`-adic completion is an equivalence. -/
@[stacks 05ET "finite principal-adic formal-gluing equivalence"]
#check (principalAdicFormalGlueingFGFunctor_isEquivalence f :
  Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f))
