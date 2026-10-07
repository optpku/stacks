module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback on small etale sites

The small etale site is a morphism-property full subcategory. This leaf gives
its base-change functor directly through Mathlib's generic over-category
pullback construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- Base change along `f` on the small etale sites of schemes. -/
noncomputable abbrev smallEtalePullback (f : T ⟶ S) :
    S.Etale ⥤ T.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

/-- Base change is continuous for the small etale topologies. -/
@[stacks 021I]
instance smallEtalePullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (smallEtalePullback f) S.smallEtaleTopology
      T.smallEtaleTopology := sorry

/-- The direct image of Type-valued sheaves along small etale base change. -/
noncomputable def smallEtaleDirectImage (f : T ⟶ S) :
    Sheaf T.smallEtaleTopology (Type v) ⥤ Sheaf S.smallEtaleTopology (Type v) :=
  (smallEtalePullback f).sheafPushforwardContinuous
    (Type v) S.smallEtaleTopology T.smallEtaleTopology

/-- Small etale base change presents a morphism of sites. -/
@[stacks 021I]
instance smallEtalePullback_isMorphismOfSites (f : T ⟶ S) :
    IsMorphismOfSites S.smallEtaleTopology T.smallEtaleTopology
      (smallEtalePullback f) := sorry

/-- Pullback of coefficient-valued sheaves on small etale sites is left adjoint to
continuous direct image. -/
noncomputable def smallEtalePullback_sheafAdjunction (f : T ⟶ S)
    (A : Type v) [Category.{w} A] [HasWeakSheafify T.smallEtaleTopology A]
    [∀ P : S.Etaleᵒᵖ ⥤ A, (smallEtalePullback f).op.HasLeftKanExtension P] :
    (smallEtalePullback f).sheafPullback A S.smallEtaleTopology T.smallEtaleTopology ⊣
      (smallEtalePullback f).sheafPushforwardContinuous
        A S.smallEtaleTopology T.smallEtaleTopology :=
  Functor.sheafAdjunctionContinuous
    (smallEtalePullback f) A S.smallEtaleTopology T.smallEtaleTopology

/-- Sheaf pullback along small etale base change preserves finite limits. -/
instance smallEtalePullback_sheafPullback_preservesFiniteLimits (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology T.smallEtaleTopology) := sorry

/-- Étale inverse image along a flat, locally finitely presented morphism with
geometrically reduced fibres preserves arbitrary products. -/
instance smallEtalePullback_sheafPullback_preservesProducts
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    {J : Type (u + 1)} :
    PreservesLimitsOfShape (Discrete J)
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology X.smallEtaleTopology) := sorry

end AlgebraicGeometry.Scheme
