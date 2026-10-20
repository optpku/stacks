module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition
public import ReasLib.CategoryTheory.Pro.Presentation
public import ReasLib.CategoryTheory.Pro.Sequential.Diagonal
public import ReasLib.CategoryTheory.InverseSystem.Positive.Sequential
public import ReasLib.CategoryTheory.Pro.RepresentedHom

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open DerivedCategory
open CategoryTheory.ObjectProperty.FullSubcategory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace CompactSupport

open Compactification.Of

/-- Canonical embedding of bounded coherent derived objects as bounded-below coherent
derived objects. -/
abbrev boundedToPlus (T : Scheme.{u}) :
    Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent T.ringCatSheaf] :=
  coherentBoundedToPlus T

/-- Forgetting boundedness after `boundedToPlus` leaves the underlying derived object
unchanged. -/
theorem boundedToPlus_obj (T : Scheme.{u})
    (K : Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf]) :
    ((boundedToPlus T).obj K).obj.obj = K.obj.obj := sorry

/-- The pro-object in the bounded coherent derived category presented by a positive
inverse system. -/
noncomputable def coherentProObject (T : Scheme.{u})
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf]) :
    Pro Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf] :=
  (@Pro.lim Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf] _
    (OrderDual ℕ+) _ _ _ _).obj A

/-- `coherentProObject` is the pro-limit of its positive inverse system. -/
theorem coherentProObject_def (T : Scheme.{u})
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf]) :
    coherentProObject T A =
      (@Pro.lim Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf] _
        (OrderDual ℕ+) _ _ _ _).obj A := sorry

/-- The compact-support functor determined by a functorial family of positive-system
presentations. -/
noncomputable def pushforwardModel
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S}
    (system : (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) →
      PNatInverseSystem Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (systemMap : ∀ {K L :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}, (K ⟶ L) →
      (coherentProObject (Over.left Y.obj) (system K) ⟶
        coherentProObject (Over.left Y.obj) (system L)))
    (systemMap_id : ∀ K, systemMap (𝟙 K) = 𝟙 _)
    (systemMap_comp : ∀ {K L M :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}
      (a : K ⟶ L) (b : L ⟶ M),
      systemMap (a ≫ b) = systemMap a ≫ systemMap b) :
    Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] where
  obj K := coherentProObject (Over.left Y.obj) (system K)
  map a := systemMap a
  map_id K := systemMap_id K
  map_comp a b := systemMap_comp a b

/-- On objects, `pushforwardModel` is the pro-object of the chosen compact-support
presentation. -/
theorem pushforwardModel_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S}
    (system : (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) →
      PNatInverseSystem Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (systemMap : ∀ {K L :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}, (K ⟶ L) →
      (coherentProObject (Over.left Y.obj) (system K) ⟶
        coherentProObject (Over.left Y.obj) (system L)))
    (systemMap_id : ∀ K, systemMap (𝟙 K) = 𝟙 _)
    (systemMap_comp : ∀ {K L M :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}
      (a : K ⟶ L) (b : L ⟶ M),
      systemMap (a ≫ b) = systemMap a ≫ systemMap b)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    (pushforwardModel system systemMap systemMap_id systemMap_comp).obj K =
      coherentProObject (Over.left Y.obj) (system K) := sorry

/-- The diagonal pro-object attached to a sequence of positive inverse systems with
sequential transitions. -/
noncomputable def iteratedProObject (T : Scheme.{u})
    (system : ℕ →
      PNatInverseSystem Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf])
    (transition : ∀ k, Pro.SequentialHom
      (system (k + 1)).toSequential (system k).toSequential) :
    Pro Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf] :=
  Pro.SequentialHom.diagonalPro (fun k ↦ (system k).toSequential) transition

/-- `iteratedProObject` is the diagonal pro-object of its sequentially reindexed rows. -/
theorem iteratedProObject_def (T : Scheme.{u})
    (system : ℕ →
      PNatInverseSystem Dᵇ[SheafOfModules.isCoherent T.ringCatSheaf])
    (transition : ∀ k, Pro.SequentialHom
      (system (k + 1)).toSequential (system k).toSequential) :
    iteratedProObject T system transition =
      Pro.SequentialHom.diagonalPro (fun k ↦ (system k).toSequential) transition := sorry

/-- The functorial diagonal model for applying compact-support pushforward along a second
morphism to the stages of a compact-support presentation along a first morphism. -/
noncomputable def iteratedPushforward
    {S : Scheme.{u}} [IsNoetherian S]
    {X Z : Scheme.FiniteTypeSeparatedOver S}
    (gSystem : (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) →
      ℕ → PNatInverseSystem
        Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf])
    (transition : ∀ K k, Pro.SequentialHom
      (gSystem K (k + 1)).toSequential (gSystem K k).toSequential)
    (iteratedMap : ∀ {K L :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}, (K ⟶ L) →
      (iteratedProObject (Over.left Z.obj) (gSystem K) (transition K) ⟶
        iteratedProObject (Over.left Z.obj) (gSystem L) (transition L)))
    (iteratedMap_id : ∀ K, iteratedMap (𝟙 K) = 𝟙 _)
    (iteratedMap_comp : ∀ {K L M :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}
      (a : K ⟶ L) (b : L ⟶ M),
      iteratedMap (a ≫ b) = iteratedMap a ≫ iteratedMap b) :
    Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf] where
  obj K := iteratedProObject (Over.left Z.obj) (gSystem K) (transition K)
  map a := iteratedMap a
  map_id K := iteratedMap_id K
  map_comp a b := iteratedMap_comp a b

/-- On objects, `iteratedPushforward` is the associated diagonal pro-object. -/
theorem iteratedPushforward_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Z : Scheme.FiniteTypeSeparatedOver S}
    (gSystem : (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) →
      ℕ → PNatInverseSystem
        Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf])
    (transition : ∀ K k, Pro.SequentialHom
      (gSystem K (k + 1)).toSequential (gSystem K k).toSequential)
    (iteratedMap : ∀ {K L :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}, (K ⟶ L) →
      (iteratedProObject (Over.left Z.obj) (gSystem K) (transition K) ⟶
        iteratedProObject (Over.left Z.obj) (gSystem L) (transition L)))
    (iteratedMap_id : ∀ K, iteratedMap (𝟙 K) = 𝟙 _)
    (iteratedMap_comp : ∀ {K L M :
        Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]}
      (a : K ⟶ L) (b : L ⟶ M),
      iteratedMap (a ≫ b) = iteratedMap a ≫ iteratedMap b)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    (iteratedPushforward gSystem transition iteratedMap iteratedMap_id
      iteratedMap_comp).obj K =
        iteratedProObject (Over.left Z.obj) (gSystem K) (transition K) := sorry

/-- The represented Hom bifunctor associated to the direct compact-support model for
`f ≫ g`, expressed through the corresponding upper-shriek functor. -/
noncomputable def compositeShriekHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf] ⥤ Type (u + 1) :=
  ((𝟭 _).prod (boundedToPlus (Over.left Z.obj))) ⋙
    shriekHom (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg.right
      C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility

/-- Objectwise, `compositeShriekHom` computes Hom into the upper-shriek model for
`f ≫ g`. -/
theorem compositeShriekHom_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf]) :
    (compositeShriekHom f g C).obj (op K, L) =
      (shriekHom (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg.right
        C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility).obj
          (op K, (boundedToPlus (Over.left Z.obj)).obj L) := sorry

/-- The represented Hom bifunctor associated to the iterated compact-support model,
expressed through `g` then `f` on upper shriek. -/
noncomputable def iteratedShriekHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf] ⥤ Type (u + 1) :=
  ((𝟭 _).prod
      (boundedToPlus (Over.left Z.obj) ⋙
        upperShriekCoherentPlus g C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility)) ⋙
    shriekHom f C.P_f C.A_f.right C.A_f.adjunction C.A_f.plus C.A_f.compatibility

/-- Objectwise, `iteratedShriekHom` computes Hom into `f` then `g` of the upper-shriek
model of `L`. -/
theorem iteratedShriekHom_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Z.obj).ringCatSheaf]) :
    (iteratedShriekHom f g C).obj (op K, L) =
      (shriekHom f C.P_f C.A_f.right C.A_f.adjunction C.A_f.plus
        C.A_f.compatibility).obj
          (op K, (upperShriekCoherentPlus g C.P_g C.A_g.right C.A_g.adjunction
            C.A_g.plus C.A_g.compatibility).obj
              ((boundedToPlus (Over.left Z.obj)).obj L)) := sorry

/-- For composable finite-type separated morphisms over a Noetherian base, the Hom
bifunctors of the direct composite compact-support model and of the iterated
compact-support model are naturally isomorphic. -/
theorem comp_isomorphic
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    Nonempty (compositeShriekHom f g C ≅ iteratedShriekHom f g C) := sorry

end CompactSupport
end ModuleDerived
end Scheme
end AlgebraicGeometry
