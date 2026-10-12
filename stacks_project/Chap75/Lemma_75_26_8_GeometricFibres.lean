/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- A morphism of algebraic spaces has reduced geometric fibres if the fibre over
every geometric point of the target is reduced. -/
@[mk_iff]
class HasReducedGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The geometric fibre over every geometric point of the target is reduced. -/
  isReduced_geometricFiber (ybar : GeometricPoint Y) :
    IsReduced (fieldFiber f ybar.toFieldValuedPoint)

namespace HasReducedGeometricFibres

/-- A morphism with reduced geometric fibres has a reduced geometric fibre over
every geometric point of the target. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasReducedGeometricFibres f] (ybar : GeometricPoint Y) :
    IsReduced (fieldFiber f ybar.toFieldValuedPoint) :=
  sorry

/-- Reducedness of every geometric fibre witnesses that a morphism of algebraic
spaces has reduced geometric fibres. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ ybar : GeometricPoint Y,
      IsReduced (fieldFiber f ybar.toFieldValuedPoint)) :
    HasReducedGeometricFibres f :=
  sorry

end HasReducedGeometricFibres

/-- The identity morphism of an algebraic space has reduced geometric fibres. -/
instance instHasReducedGeometricFibres_id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    HasReducedGeometricFibres (𝟙 X) :=
  sorry

/-- If `f` is proper and has reduced and connected geometric fibres, then every
field-valued fibre satisfies `k = Γ(X_k, 𝒪_{X_k})`. -/
theorem fiberGlobalSectionsBijective_of_reducedConnectedGeometricFibres
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [HasReducedGeometricFibres f] [HasConnectedGeometricFibres f] :
    fiberGlobalSectionsBijective f :=
  sorry

/-- If `f` is proper, flat, and of finite presentation, and the geometric fibres of
`f` are reduced and connected, then the canonical map `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism. -/
instance structureSheafMap_isIso_of_reducedConnectedGeometricFibres
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [HasReducedGeometricFibres f] [HasConnectedGeometricFibres f] :
    IsIso (structureSheafMap f) :=
  sorry

/-- Under the same hypotheses, the canonical structure-sheaf pushforward map remains an
isomorphism after every base change. -/
instance baseChange_structureSheafMap_isIso_of_reducedConnectedGeometricFibres
    {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [HasReducedGeometricFibres f] [HasConnectedGeometricFibres f]
    (g : Y' ⟶ Y) :
    IsIso (structureSheafMap (pullback.snd f g)) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
