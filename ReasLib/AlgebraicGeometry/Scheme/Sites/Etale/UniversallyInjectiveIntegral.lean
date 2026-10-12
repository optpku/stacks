/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AlmostCocontinuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.IntegralPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Reflection
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.CategoryTheory.Adjunction.EpiMono
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [UniversallyInjective f] [IsIntegralHom f]

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- An integral universally injective morphism has Property (C). -/
theorem hasPropertyC_of_universallyInjective_integral : hasPropertyC f := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig

namespace AlgebraicGeometry.SmallEtale

/-- The small étale direct image reflects monomorphisms for an integral universally injective morphism. -/
instance pushforward_reflectsMonomorphisms
    [HasSheafify X.smallEtaleTopology (Type (u + 1))] :
    (smallMorphism f).pushforward.ReflectsMonomorphisms := sorry

/-- The small étale direct image reflects epimorphisms for an integral universally injective morphism. -/
instance pushforward_reflectsEpimorphisms
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasSheafify Y.smallEtaleTopology (Type (u + 1))] :
    (smallMorphism f).pushforward.ReflectsEpimorphisms := sorry

/-- The small étale direct image preserves finite connected colimits for an integral universally injective morphism. -/
instance pushforward_preservesFiniteConnectedColimits
    [HasSheafify X.smallEtaleTopology (Type (u + 1))] :
    PreservesFiniteConnectedColimits (smallMorphism f).pushforward := sorry

/-- Every counit component of the small étale direct image is epic for an integral universally injective morphism. -/
instance pushforward_counit_epi
    [HasSheafify X.smallEtaleTopology (Type (u + 1))] :
    ∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Epi ((smallMorphism f).adjunction.counit.app F) := sorry

/-- The small étale direct image is faithful for an integral universally injective morphism. -/
instance pushforward_faithful
    [HasSheafify X.smallEtaleTopology (Type (u + 1))] :
    (smallMorphism f).pushforward.Faithful := sorry

/-- Pullback between the small étale sites is almost cocontinuous for an integral universally injective morphism. -/
instance pullback_isAlmostCocontinuous :
    Functor.IsAlmostCocontinuous (Scheme.smallEtalePullback f)
      Y.smallEtaleTopology X.smallEtaleTopology := sorry

end AlgebraicGeometry.SmallEtale
