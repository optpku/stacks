module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pushforward.GeometricFibres
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap75.Lemma_75_26_7_StructureSheaf
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_GeometricallyConnected

/-!
# Reduced geometric fibres and structure-sheaf pushforward

A morphism of algebraic spaces has reduced geometric fibres when every
geometric fibre is a reduced algebraic space. Combined with connectedness of
geometric fibres, properness yields fibrewise bijectivity of `k → Γ(X_k, 𝒪_{X_k})`,
and with flatness and finite presentation the canonical map `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism, including after arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.HasReducedGeometricFibres :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.hasReducedGeometricFibres_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Hom.HasReducedGeometricFibres f ↔
      ∀ ybar : GeometricPoint Y, IsReduced (fieldFiber f ybar.toFieldValuedPoint))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.HasReducedGeometricFibres.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Hom.HasReducedGeometricFibres f] (ybar : GeometricPoint Y),
    IsReduced (fieldFiber f ybar.toFieldValuedPoint))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.HasReducedGeometricFibres.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    (∀ ybar : GeometricPoint Y, IsReduced (fieldFiber f ybar.toFieldValuedPoint)) →
      Hom.HasReducedGeometricFibres f)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.instHasReducedGeometricFibres_id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, Hom.HasReducedGeometricFibres (𝟙 X))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.fiberGlobalSectionsBijective_of_reducedConnectedGeometricFibres :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Hom.HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f],
      fiberGlobalSectionsBijective f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.structureSheafMap_isIso_of_reducedConnectedGeometricFibres :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f]
      [Hom.HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f],
      IsIso (structureSheafMap f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.baseChange_structureSheafMap_isIso_of_reducedConnectedGeometricFibres :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f]
      [Hom.HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f],
      ∀ g : Y' ⟶ Y, IsIso (structureSheafMap (pullback.snd f g)))
