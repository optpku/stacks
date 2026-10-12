/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.BaseChange.Isomorphism
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Composition.Plus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.LeftDerived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A bounded-below model of a right adjoint to derived pushforward, together with its
comparison to the chosen unbounded right adjoint. -/
structure PlusRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] where
  /-- The chosen right adjoint on unbounded derived categories. -/
  right : DerivedQCoh Y ⥤ DerivedQCoh X
  /-- The adjunction exhibiting `right` as the right adjoint to derived pushforward. -/
  adjunction : pushforwardCohomologyIn f ⊣ right
  /-- The bounded-below restriction of the chosen right adjoint. -/
  plus : Plus Y ⥤ Plus X
  /-- Compatibility of the bounded-below model with the unbounded right adjoint. -/
  compatibility :
    plus ⋙ DerivedCategory.Plus.CohomologyIn.ambient
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
        right ⋙ inclusion X

/-- The compatibility of a bounded-below right-adjoint model before forgetting
quasicoherence. -/
noncomputable def PlusRightAdjoint.restrictionIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (A : PlusRightAdjoint f) :
    A.plus ⋙ DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙ A.right :=
  ((ObjectProperty.fullyFaithfulι
    (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))).whiskeringRight
        (Plus Y)).preimageIso A.compatibility

/-- Lift a natural transformation between unbounded right-adjoint models to their specified
bounded-below restrictions. -/
noncomputable def PlusRightAdjoint.map
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (A B : PlusRightAdjoint f) (alpha : A.right ⟶ B.right) : A.plus ⟶ B.plus :=
  (((ObjectProperty.fullyFaithfulι
      (DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))).comp
      DerivedCategory.TStructure.t.plus.fullyFaithfulι).whiskeringRight (Plus Y)).preimage
    (A.compatibility.hom ≫
      Functor.whiskerLeft
        (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace))
        (Functor.whiskerRight alpha (inclusion X)) ≫
      B.compatibility.inv)

/-- An invertible unbounded comparison lifts to an invertible comparison of the specified
bounded-below right-adjoint models. -/
theorem PlusRightAdjoint.map_isIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (A B : PlusRightAdjoint f) (alpha : A.right ⟶ B.right) [IsIso alpha] :
    IsIso (A.map B alpha) := sorry

/-- The canonical isomorphism between two bounded-below models of right adjoints to the same
derived pushforward functor. -/
noncomputable def PlusRightAdjoint.iso
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (A B : PlusRightAdjoint f) : A.plus ≅ B.plus :=
  @asIso _ _ _ _ (A.map B (A.adjunction.rightAdjointUniq B.adjunction).hom)
    (A.map_isIso B (A.adjunction.rightAdjointUniq B.adjunction).hom)

/-- The canonical compatibility of a composite bounded-below model with the composite
unbounded right adjoint. -/
noncomputable def PlusRightAdjoint.compRestrictionIso
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (A : PlusRightAdjoint f) (B : PlusRightAdjoint g) :
    (B.plus ⋙ A.plus) ⋙ DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.toRingedSpace) ⋙
        (B.right ⋙ A.right) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft B.plus A.restrictionIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight B.restrictionIso A.right ≪≫
    Functor.associator _ _ _

/-- The composite bounded-below model agrees with the composite unbounded right adjoint
after passage to the ambient derived category. -/
noncomputable def PlusRightAdjoint.compCompatibility
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (A : PlusRightAdjoint f) (B : PlusRightAdjoint g) :
    (B.plus ⋙ A.plus) ⋙ DerivedCategory.Plus.CohomologyIn.ambient
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.toRingedSpace) ⋙
        (B.right ⋙ A.right) ⋙ inclusion X :=
  Functor.isoWhiskerRight (A.compRestrictionIso B) (inclusion X)

/-- Compose two bounded-below right-adjoint models using the canonical composition
adjunction and compatibility comparison. -/
noncomputable def PlusRightAdjoint.comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)]
    (A : PlusRightAdjoint f) (B : PlusRightAdjoint g) : PlusRightAdjoint (f ≫ g) where
  right := B.right ⋙ A.right
  adjunction := compositeRightAdjunction f g
    (RingedSpace.modulePullbackDerived.compComparison_isIso f.toShHom g.toShHom)
    A.right B.right A.adjunction B.adjunction
  plus := B.plus ⋙ A.plus
  compatibility := A.compCompatibility B

namespace OpenImmersion

/-- The canonical comparison from exact derived pullback along an open immersion to the
chosen total derived pullback. -/
noncomputable def exactPullbackComparison {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.exactPullback j).mapDerivedCategory ⟶
      RingedSpace.modulePullbackDerived j.toShHom :=
  ExactFunctor.LeftDerived.comparison
    (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.exactPullback j)
    (RingedSpace.modulePullbackDerived j.toShHom)
    ((RingedSpace.modulePullbackToDerived j.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace))
    (inferInstanceAs
      (((RingedSpace.modulePullbackToDerived j.toShHom).totalLeftDerived
          DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).IsLeftDerivedFunctor
        ((RingedSpace.modulePullbackToDerived j.toShHom).totalLeftDerivedCounit
          DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace))
        (RingedSpace.ModuleQis X.toRingedSpace)))

/-- Exact derived pullback and total derived pullback agree along an open immersion. -/
theorem exactPullbackComparison_isIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : IsIso (exactPullbackComparison j) := sorry

/-- The canonical isomorphism from exact derived pullback along an open immersion to total
derived pullback. -/
noncomputable def exactPullbackIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.exactPullback j).mapDerivedCategory ≅
      RingedSpace.modulePullbackDerived j.toShHom :=
  @asIso _ _ _ _ (exactPullbackComparison j) (exactPullbackComparison_isIso j)

/-- Bounded-below pullback along an open immersion agrees with unbounded derived
pullback after forgetting the boundedness condition. -/
noncomputable def pullbackPlusAmbientIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    pullbackPlus j ⋙ DerivedCategory.Plus.CohomologyIn.ambient
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
        DerivedQCoh.pullback j ⋙ inclusion U :=
  let E := AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.exactPullback j
  let leftComparison :
      pullbackPlus j ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace) ≅
        DerivedCategory.Plus.CohomologyIn.ambient
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
          RingedSpace.modulePullbackDerived j.toShHom :=
    Functor.isoWhiskerRight
        (ObjectProperty.FullSubcategory.restrict.compιIso
          (ExactFunctor.Derived.Plus.functor E) (pullbackPlusMapsTo j))
        DerivedCategory.Plus.ι ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ExactFunctor.Derived.Plus.compιIso E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft _ (exactPullbackIso j)
  let rightComparison :
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
          DerivedQCoh.pullback j) ⋙ inclusion U ≅
        DerivedCategory.Plus.CohomologyIn.ambient
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
          RingedSpace.modulePullbackDerived j.toShHom :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedQCoh.pullback.inclusionIso j) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
        (RingedSpace.modulePullbackDerived j.toShHom)
  leftComparison ≪≫ rightComparison.symm

/-- Bounded-below pullback agrees with unbounded pullback before forgetting
quasicoherence. -/
noncomputable def pullbackPlusRestrictionIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    pullbackPlus j ⋙ DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
        DerivedQCoh.pullback j :=
  ((ObjectProperty.fullyFaithfulι
    (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace))).whiskeringRight
        (Plus X)).preimageIso (pullbackPlusAmbientIso j)

end OpenImmersion

/-- Restricting a bounded-below right-adjoint model along an open immersion agrees with
first forgetting boundedness and then applying the two unbounded functors. -/
noncomputable def PlusRightAdjoint.openRestrictionAmbientIso
    {X Y U : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (A : PlusRightAdjoint f) (j : U ⟶ X) [IsOpenImmersion j] :
    (A.plus ⋙ OpenImmersion.pullbackPlus j) ⋙ DerivedCategory.Plus.CohomologyIn.ambient
        (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace) ≅
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙ A.right) ⋙
        (DerivedQCoh.pullback j ⋙ inclusion U) :=
  let restrictionComparison :
      (A.plus ⋙ OpenImmersion.pullbackPlus j) ⋙
          DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty U.toRingedSpace) ≅
        (DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙ A.right) ⋙
          DerivedQCoh.pullback j :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.plus (OpenImmersion.pullbackPlusRestrictionIso j) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight A.restrictionIso (DerivedQCoh.pullback j) ≪≫
      Functor.associator _ _ _
  Functor.isoWhiskerRight restrictionComparison (inclusion U)

/-- Lift an isomorphism detected after forgetting bounded-below quasicoherent objects to
the bounded-below category. -/
noncomputable def Plus.isoOfAmbientIso {X Y : Scheme.{u}}
    (F G : Plus X ⥤ Plus Y)
    (e : F ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ≅
        G ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)) : F ≅ G :=
  (((ObjectProperty.fullyFaithfulι
      (DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace))).comp
      DerivedCategory.TStructure.t.plus.fullyFaithfulι).whiskeringRight
        (Plus X)).preimageIso e

/-- The canonical dual base-change isomorphism for a cartesian square whose horizontal
base-change morphism is flat. -/
noncomputable def PlusRightAdjoint.dualBaseChangeIso
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat g]
    (sq : IsPullback g' f' f g) (A : PlusRightAdjoint f) (A' : PlusRightAdjoint f') :
    A'.right ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ A.right :=
  @asIso _ _ _ _
    (BaseChange.rightMate g' f' f g sq.toCommSq A.right A'.right
      A.adjunction A'.adjunction)
    (BaseChange.rightMate_isIso_of_flat g' f' f g sq A.right A'.right
      A.adjunction A'.adjunction)

/-- The exceptional base-change map for a cartesian square with proper vertical maps and
flat open horizontal maps over a Noetherian base is invertible on bounded-below objects. -/
theorem PlusRightAdjoint.openBaseChangeApp_isIso
    {X' X Y' Y : Scheme.{u}}
    [IsNoetherian Y]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [IsProper f'] [IsOpenImmersion g] [IsOpenImmersion g']
    (sq : IsPullback g' f' f g) (A : PlusRightAdjoint f) (A' : PlusRightAdjoint f')
    (K : Plus Y) :
    IsIso (rightAdjointBaseChangeMap g' g A.right A'.right
      (A.dualBaseChangeIso g' f' f g sq A')
      ((DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).obj K)) := sorry

/-- Naturality of the bounded-below exceptional base-change components. -/
theorem PlusRightAdjoint.openBaseChange_naturality
    {X' X Y' Y : Scheme.{u}}
    [IsNoetherian Y]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [IsProper f'] [IsOpenImmersion g] [IsOpenImmersion g']
    (sq : IsPullback g' f' f g) (A : PlusRightAdjoint f) (A' : PlusRightAdjoint f')
    {K L : Plus Y} (φ : K ⟶ L) :
    ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
        (A.right ⋙ pullback g')).map φ) ≫
        rightAdjointBaseChangeMap g' g A.right A'.right
          (A.dualBaseChangeIso g' f' f g sq A')
          ((DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).obj L) =
      rightAdjointBaseChangeMap g' g A.right A'.right
          (A.dualBaseChangeIso g' f' f g sq A')
          ((DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).obj K) ≫
        ((DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
          (pullback g ⋙ A'.right)).map φ) := sorry

/-- The canonical exceptional base-change isomorphism on bounded-below objects. -/
noncomputable def PlusRightAdjoint.openBaseChangeIso
    {X' X Y' Y : Scheme.{u}}
    [IsNoetherian Y]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [IsProper f'] [IsOpenImmersion g] [IsOpenImmersion g']
    (sq : IsPullback g' f' f g) (A : PlusRightAdjoint f) (A' : PlusRightAdjoint f') :
    DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
        (A.right ⋙ pullback g') ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
        (pullback g ⋙ A'.right) :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _
      (rightAdjointBaseChangeMap g' g A.right A'.right
        (A.dualBaseChangeIso g' f' f g sq A')
        ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).obj K))
      (A.openBaseChangeApp_isIso g' f' f g sq A' K))
    (fun φ ↦ A.openBaseChange_naturality g' f' f g sq A' φ)

end AlgebraicGeometry.Scheme.DerivedQCoh
