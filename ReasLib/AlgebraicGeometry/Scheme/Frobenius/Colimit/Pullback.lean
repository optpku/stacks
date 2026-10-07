module

public import Mathlib.CategoryTheory.Core
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.VectorBundle
public import ReasLib.CategoryTheory.Functor.AsSmall
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Identity

/-!
# Pullback on Frobenius-colimit module models

This module constructs pullback both on vector bundles and on finite locally free modules over
Frobenius-colimit structure sheaves.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

/-- Pullback along a scheme morphism preserves finite locally free module sheaves. -/
theorem vectorBundlesPullback_mapsTo {S T : Scheme.{u}} (f : T ⟶ S) :
    (fun E : S.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E) ≤
      ObjectProperty.inverseImage
        (fun E : T.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E)
        (Scheme.Modules.pullback f) := sorry

/-- Pullback along a scheme morphism, restricted to the small categories of vector bundles. -/
def vectorBundlesPullback {S T : Scheme.{u}} (f : T ⟶ S) :
    vectorBundles S ⥤ vectorBundles T :=
  AsSmall.down ⋙
    ObjectProperty.FullSubcategory.restrict
      (Scheme.Modules.pullback f) (vectorBundlesPullback_mapsTo f) ⋙
    AsSmall.up

/-- The underlying module of restricted vector-bundle pullback is ordinary module pullback. -/
theorem vectorBundlesPullback_obj {S T : Scheme.{u}} (f : T ⟶ S)
    (E : vectorBundles S) :
    (ULift.down ((vectorBundlesPullback f).obj E)).obj =
      (Scheme.Modules.pullback f).obj (ULift.down E).obj := sorry

/-- A functor between Frobenius colimits is stagewise pullback along a scheme morphism when it
agrees with ordinary vector-bundle pullback at every Frobenius stage. -/
class IsStagewisePullback.{v} (p : ℕ) [Fact p.Prime] {S T : Scheme.{v}}
    [S.IsCharP p] [T.IsCharP p] (f : T ⟶ S)
    (G : vectorBundleColimit p S ⥤ vectorBundleColimit p T) : Prop where
  stageIso (n : ℕ) : Nonempty
    (stage p S n ⋙ G ≅ vectorBundlesPullback f ⋙ stage p T n)

/-- Stagewise pullback is equivalent to the existence of the displayed natural isomorphism at
every Frobenius stage. -/
theorem isStagewisePullback_iff (p : ℕ) [Fact p.Prime] {S T : Scheme.{u}}
    [S.IsCharP p] [T.IsCharP p] (f : T ⟶ S)
    (G : vectorBundleColimit p S ⥤ vectorBundleColimit p T) :
    IsStagewisePullback p f G ↔ ∀ n, Nonempty
      (stage p S n ⋙ G ≅ vectorBundlesPullback f ⋙ stage p T n) := sorry

/-- The identity functor is stagewise pullback along the identity scheme morphism. -/
instance instIsStagewisePullbackId (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] :
    IsStagewisePullback p (𝟙 S) (𝟭 (vectorBundleColimit p S)) := sorry

/-- A composite of stagewise pullback functors is stagewise pullback along the composite scheme
morphism. -/
instance instIsStagewisePullbackComp (p : ℕ) [Fact p.Prime]
    {S T U : Scheme.{u}} [S.IsCharP p] [T.IsCharP p] [U.IsCharP p]
    (f : T ⟶ S) (g : U ⟶ T)
    (F : vectorBundleColimit p S ⥤ vectorBundleColimit p T)
    (G : vectorBundleColimit p T ⥤ vectorBundleColimit p U)
    [IsStagewisePullback p f F] [IsStagewisePullback p g G] :
    IsStagewisePullback p (g ≫ f) (F ⋙ G) := sorry

namespace ModuleModel

/-- The space underlying a scheme, equipped with its Frobenius-colimit sheaf of rings. -/
def ringedSpace (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [X.IsCharP p] :
    SheafedSpace RingCat.{u} where
  carrier := X
  presheaf := (ringSheaf p X).presheaf
  IsSheaf := (ringSheaf p X).2

/-- The underlying topological space of the Frobenius-colimit ringed space is the scheme's
underlying space. -/
theorem ringedSpace_carrier (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [X.IsCharP p] :
    (ringedSpace p X : TopCat) = X := sorry

/-- The structure sheaf of the Frobenius-colimit ringed space is the Frobenius-colimit sheaf. -/
theorem ringedSpace_sheaf (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [X.IsCharP p] :
    (ringedSpace p X).sheaf = ringSheaf p X := sorry

/-- The maps from the Frobenius stages on the target to the pushforward of the colimit sheaf on
the source form a cocone. -/
theorem mapCocone_naturality (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) {i j : ℕ} (g : i ⟶ j) :
    (ringSheafDiagram p Y).map g ≫
        RingedSpace.Hom.toRingCatSheafHom f.toShHom ≫
          (TopCat.Sheaf.pushforward RingCat.{u} f.base).map (toRingSheaf p X j) =
      RingedSpace.Hom.toRingCatSheafHom f.toShHom ≫
          (TopCat.Sheaf.pushforward RingCat.{u} f.base).map (toRingSheaf p X i) ≫
        ((Functor.const ℕ).obj
          ((TopCat.Sheaf.pushforward RingCat.{u} f.base).obj (ringSheaf p X))).map g := sorry

/-- The cocone on the target's Frobenius diagram obtained by pushing forward the source's
Frobenius-colimit sheaf along a scheme morphism. -/
def mapCocone (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) : Cocone (ringSheafDiagram p Y) where
  pt := (TopCat.Sheaf.pushforward RingCat.{u} f.base).obj (ringSheaf p X)
  ι :=
    { app := fun n ↦ RingedSpace.Hom.toRingCatSheafHom f.toShHom ≫
        (TopCat.Sheaf.pushforward RingCat.{u} f.base).map (toRingSheaf p X n)
      naturality := fun {_ _} g ↦ mapCocone_naturality p f g }

/-- The leg of the induced Frobenius-colimit cocone at a specified stage. -/
theorem mapCocone_ι (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) (n : ℕ) :
    (mapCocone p f).ι.app n =
      RingedSpace.Hom.toRingCatSheafHom f.toShHom ≫
        (TopCat.Sheaf.pushforward RingCat.{u} f.base).map (toRingSheaf p X n) := sorry

/-- A scheme morphism induces a morphism between the corresponding Frobenius-colimit ringed
spaces. -/
def map (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) : ringedSpace p X ⟶ ringedSpace p Y :=
  InducedCategory.homMk
    { base := f.base
      c := (ringSheafDesc p Y (mapCocone p f)).hom }

/-- The underlying continuous map of the induced Frobenius-colimit ringed-space morphism is the
map underlying the scheme morphism. -/
theorem map_base (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) :
    (map p f).hom.base = f.base := sorry

/-- The Frobenius-colimit ringed-space construction preserves identity morphisms. -/
theorem map_id (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [X.IsCharP p] :
    map p (𝟙 X) = 𝟙 (ringedSpace p X) := sorry

/-- The Frobenius-colimit ringed-space construction preserves composition. -/
theorem map_comp (p : ℕ) [Fact p.Prime] {X Y Z : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] [Z.IsCharP p] (f : X ⟶ Y) (g : Y ⟶ Z) :
    map p (f ≫ g) = map p f ≫ map p g := sorry

/-- Pullback along the induced Frobenius-colimit ringed-space morphism preserves finite locally
free module sheaves. -/
theorem pullback_mapsTo (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) :
    (fun E : SheafOfModules.{u} (ringSheaf p Y) ↦
      SheafOfModules.IsFiniteLocallyFree E) ≤
      ObjectProperty.inverseImage
        (fun E : SheafOfModules.{u} (ringSheaf p X) ↦
          SheafOfModules.IsFiniteLocallyFree E)
        (SheafOfModules.pullback
          (⟨(map p f).hom.c⟩ : ringSheaf p Y ⟶
            (TopCat.Sheaf.pushforward RingCat.{u} f.base).obj (ringSheaf p X))) := sorry

/-- Pullback along a scheme morphism on finite locally free modules over Frobenius-colimit
structure sheaves. -/
def pullback (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) :
    finiteLocallyFreeModules p Y ⥤ finiteLocallyFreeModules p X :=
  Functor.asSmall.{u + 1}
    (ObjectProperty.FullSubcategory.restrict
      (SheafOfModules.pullback
        (⟨(map p f).hom.c⟩ : ringSheaf p Y ⟶
          (TopCat.Sheaf.pushforward RingCat.{u} f.base).obj (ringSheaf p X)))
      (pullback_mapsTo p f))

/-- The underlying module of restricted pullback is ordinary module-sheaf pullback along the
induced Frobenius-colimit ringed-space morphism. -/
theorem pullback_obj (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y)
    (E : finiteLocallyFreeModules p Y) :
    (ULift.down ((pullback p f).obj E)).obj =
      (SheafOfModules.pullback
        (⟨(map p f).hom.c⟩ : ringSheaf p Y ⟶
          (TopCat.Sheaf.pushforward RingCat.{u} f.base).obj (ringSheaf p X))).obj
        (ULift.down E).obj := sorry

/-- Restricted pullback along the identity scheme morphism is the identity functor. -/
theorem pullbackIdIso_hom (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [X.IsCharP p] :
    pullback p (𝟙 X) = 𝟭 (finiteLocallyFreeModules p X) := sorry

/-- The canonical identity comparison for restricted pullback over Frobenius-colimit sheaves. -/
def pullbackIdIso (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [X.IsCharP p] :
    pullback p (𝟙 X) ≅ 𝟭 (finiteLocallyFreeModules p X) :=
  eqToIso (pullbackIdIso_hom p X)

/-- Restricted pullback along a composite is the composite of the two restricted pullback
functors. -/
theorem pullbackCompIso_hom (p : ℕ) [Fact p.Prime] {X Y Z : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] [Z.IsCharP p] (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback p (f ≫ g) = pullback p g ⋙ pullback p f := sorry

/-- The canonical composition comparison for restricted pullback over Frobenius-colimit
sheaves. -/
def pullbackCompIso (p : ℕ) [Fact p.Prime] {X Y Z : Scheme.{u}}
    [X.IsCharP p] [Y.IsCharP p] [Z.IsCharP p] (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback p (f ≫ g) ≅ pullback p g ⋙ pullback p f :=
  eqToIso (pullbackCompIso_hom p f g)

end ModuleModel

end AlgebraicGeometry.Scheme.FrobeniusColimit
