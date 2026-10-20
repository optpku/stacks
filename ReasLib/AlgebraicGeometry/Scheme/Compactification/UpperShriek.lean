module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Existence
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace FiniteTypeSeparatedOver

/-- An object separated and of finite type over a Noetherian scheme is Noetherian. -/
instance instIsNoetherian {S : Scheme.{u}} [IsNoetherian S]
    (X : FiniteTypeSeparatedOver S) : IsNoetherian X.obj.left := sorry

end FiniteTypeSeparatedOver

namespace Compactification.Of

/-- The ambient scheme of a compactification over a Noetherian base is Noetherian. -/
instance instAmbientIsNoetherian {S : Scheme.{u}} [IsNoetherian S]
    {X : Over S} (P : Of S X) : IsNoetherian P.obj.right.left := sorry

/-- A morphism between schemes separated and of finite type over a Noetherian base admits a
compactification over its target. -/
instance instNonempty {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    Nonempty (Of Y.obj.left (Over.mk f.hom.left)) := sorry

/-- The upper-shriek functor attached to a compactification `P` applies a bounded-below
right-adjoint model and then restricts along the fixed open interior. -/
noncomputable def upperShriek
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (aPlus : DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left) :
    DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left :=
  aPlus ⋙ @DerivedQCoh.OpenImmersion.pullbackPlus _ _ (ι P)
    P.property.isOpenImmersion

/-- The displayed formula for the upper-shriek functor associated to a compactification. -/
theorem upperShriek_def
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (aPlus : DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left) :
    upperShriek f P aPlus =
      aPlus ⋙ @DerivedQCoh.OpenImmersion.pullbackPlus _ _ (ι P)
        P.property.isOpenImmersion := sorry

/-- Form the upper-shriek comparison associated to a specified dense common refinement. -/
noncomputable def upperShriekIsoOfDenseRefinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P, comparison.obj P ≅ upperShriek f P (aPlus P))
    {P Q : Of Y.obj.left (Over.mk f.hom.left)}
    (R : Compactification.DenseOf Y.obj.left (Over.mk f.hom.left))
    (p : (Compactification.DenseOf.inclusion Y.obj.left
      (Over.mk f.hom.left)).obj R ⟶ P)
    (q : (Compactification.DenseOf.inclusion Y.obj.left
      (Over.mk f.hom.left)).obj R ⟶ Q)
    (hp : IsIso (comparison.map p)) (hq : IsIso (comparison.map q)) :
    upperShriek f P (aPlus P) ≅ upperShriek f Q (aPlus Q) :=
  (modelIso P).symm ≪≫ (@asIso _ _ _ _ (comparison.map p) hp).symm ≪≫
    @asIso _ _ _ _ (comparison.map q) hq ≪≫ modelIso Q

/-- The forward map of the dense-refinement comparison is the composite of the comparison maps
and the objectwise model identifications. -/
theorem upperShriekIsoOfDenseRefinement_hom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P, comparison.obj P ≅ upperShriek f P (aPlus P))
    {P Q : Of Y.obj.left (Over.mk f.hom.left)}
    (R : Compactification.DenseOf Y.obj.left (Over.mk f.hom.left))
    (p : (Compactification.DenseOf.inclusion Y.obj.left
      (Over.mk f.hom.left)).obj R ⟶ P)
    (q : (Compactification.DenseOf.inclusion Y.obj.left
      (Over.mk f.hom.left)).obj R ⟶ Q)
    (hp : IsIso (comparison.map p)) (hq : IsIso (comparison.map q)) :
    (upperShriekIsoOfDenseRefinement f aPlus comparison modelIso R p q hp hq).hom =
      (modelIso P).inv ≫ (@asIso _ _ _ _ (comparison.map p) hp).inv ≫
        (@asIso _ _ _ _ (comparison.map q) hq).hom ≫ (modelIso Q).hom := sorry

/-- The explicit upper-shriek comparison obtained from a cofiltered dense refinement and
specified right-adjoint and bounded-below model data. -/
noncomputable def upperShriekIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (a : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh Y.obj.left ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a P)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      aPlus P ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
          a P ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      comparison.obj P ≅ upperShriek f P (aPlus P))
    (comparisonIsIso : ∀ {P Q : Of Y.obj.left (Over.mk f.hom.left)} (g : P ⟶ Q),
      IsDominant (ι P) → IsIso (comparison.map g))
    (P Q : Of Y.obj.left (Over.mk f.hom.left)) :
    upperShriek f P (aPlus P) ≅ upperShriek f Q (aPlus Q) :=
  let inclusion := Compactification.DenseOf.inclusion Y.obj.left (Over.mk f.hom.left)
  let common := IsCofiltered.min P Q
  let dense := Functor.Initial.lift inclusion common
  let toCommon := Functor.Initial.homToLift inclusion common
  upperShriekIsoOfDenseRefinement f aPlus comparison modelIso dense
    (toCommon ≫ IsCofiltered.minToLeft P Q)
    (toCommon ≫ IsCofiltered.minToRight P Q)
    (comparisonIsIso _ dense.property.isDominant)
    (comparisonIsIso _ dense.property.isDominant)

/-- The explicit upper-shriek comparison agrees with the comparison from every dense common
refinement. -/
theorem upperShriekIso_eq_of_dense_refinement
    {S : Scheme.{u}} [hS : IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (a : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh Y.obj.left ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a P)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      aPlus P ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
          a P ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      comparison.obj P ≅ upperShriek f P (aPlus P))
    (comparisonIsIso : ∀ {P Q : Of Y.obj.left (Over.mk f.hom.left)} (g : P ⟶ Q),
      IsDominant (ι P) → IsIso (comparison.map g))
    (P Q : Of Y.obj.left (Over.mk f.hom.left))
    (R : Compactification.DenseOf Y.obj.left (Over.mk f.hom.left))
    (p : (Compactification.DenseOf.inclusion Y.obj.left
      (Over.mk f.hom.left)).obj R ⟶ P)
    (q : (Compactification.DenseOf.inclusion Y.obj.left
      (Over.mk f.hom.left)).obj R ⟶ Q) :
    upperShriekIso f a aAdjunction aPlus aPlusCompatibility comparison modelIso
        comparisonIsIso P Q =
      upperShriekIsoOfDenseRefinement f aPlus comparison modelIso R p q
        (comparisonIsIso p R.property.isDominant)
        (comparisonIsIso q R.property.isDominant) := sorry

/-- The explicit upper-shriek comparison from a compactification to itself is the identity. -/
theorem upperShriekIso_refl
    {S : Scheme.{u}} [hS : IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (a : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh Y.obj.left ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a P)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      aPlus P ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
          a P ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      comparison.obj P ≅ upperShriek f P (aPlus P))
    (comparisonIsIso : ∀ {P Q : Of Y.obj.left (Over.mk f.hom.left)} (g : P ⟶ Q),
      IsDominant (ι P) → IsIso (comparison.map g))
    (P : Of Y.obj.left (Over.mk f.hom.left)) :
    upperShriekIso f a aAdjunction aPlus aPlusCompatibility comparison modelIso
      comparisonIsIso P P = Iso.refl _ := sorry

/-- Explicit upper-shriek comparisons satisfy the cocycle law for three compactifications. -/
theorem upperShriekIso_trans
    {S : Scheme.{u}} [hS : IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (a : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh Y.obj.left ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a P)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      aPlus P ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
          a P ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      comparison.obj P ≅ upperShriek f P (aPlus P))
    (comparisonIsIso : ∀ {P Q : Of Y.obj.left (Over.mk f.hom.left)} (g : P ⟶ Q),
      IsDominant (ι P) → IsIso (comparison.map g))
    (P Q R : Of Y.obj.left (Over.mk f.hom.left)) :
    @upperShriekIso S hS X Y f a aAdjunction aPlus aPlusCompatibility comparison modelIso
        comparisonIsIso P Q ≪≫
      @upperShriekIso S hS X Y f a aAdjunction aPlus aPlusCompatibility comparison modelIso
        comparisonIsIso Q R =
      @upperShriekIso S hS X Y f a aAdjunction aPlus aPlusCompatibility comparison modelIso
        comparisonIsIso P R := sorry

/-- Compatible indexed right-adjoint and bounded-below models give isomorphic upper-shriek
functors for any two compactifications of a finite-type separated morphism. -/
theorem upperShriek_independent
    {S : Scheme.{u}} [hS : IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (a : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh Y.obj.left ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a P)
    (aPlus : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility : ∀ P : Of Y.obj.left (Over.mk f.hom.left),
      aPlus P ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
          a P ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (P Q : Of Y.obj.left (Over.mk f.hom.left)) :
    IsIsomorphic (upperShriek f P (aPlus P)) (upperShriek f Q (aPlus Q)) := sorry

end Compactification.Of

end AlgebraicGeometry.Scheme
