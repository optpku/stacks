module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Devissage
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 30.12.5: For a Noetherian scheme and an integral closed representative of an
irreducible closed support, a two-out-of-three property that holds on ideal-sheaf pushforwards
from proper integral closed subsets and on one generically rank-one coherent model holds for
every coherent sheaf supported there. -/
@[stacks 01YH]
#check (AlgebraicGeometry.Scheme.Modules.devissagePropertyHoldsOfIdealPushforwardsAndGenericRankOne :
  {X : Scheme.{u}} → [IsNoetherian X] →
  (Z₀ : X.IdealSheafData) → [IsIntegral Z₀.subscheme] →
  (ξ : X) → IsGenericPoint ξ (Z₀.support : Set X) →
  (P : X.Modules → Prop) →
  AlgebraicGeometry.Scheme.Modules.DevissageTwoOutOfThreeOnSupport Z₀ P →
  (∀ (Z : X.IdealSheafData), [IsIntegral Z.subscheme] →
    (Z.support : Set X) ⊂ (Z₀.support : Set X) →
    ∀ I : Subobject
      (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
      (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
      P ((Scheme.Modules.pushforward Z.subschemeι).obj
        (Subobject.underlying.obj I : Z.subscheme.Modules))) →
  (∃ 𝒢 : X.Modules,
    AlgebraicGeometry.Scheme.Modules.DevissageGenericRankOneSheaf Z₀ ξ P 𝒢) →
  (ℱ : X.Modules) → [ℱ.IsCoherent] →
  RingedSpace.moduleSupport ℱ ⊆ (Z₀.support : Set X) →
  P ℱ)
