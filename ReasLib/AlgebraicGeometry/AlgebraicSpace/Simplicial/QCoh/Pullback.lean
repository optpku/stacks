module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-! # Quasi-coherent pullback and pushforward along a spaces-étale augmentation -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open Functor
open RingedSite RingedSite.ToposHom
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Pullback of modules along the spaces-étale augmentation preserves quasi-coherence. -/
theorem modulePullback_le_inverseImage :
    spacesQuasiCoherentModuleProperty X ≤
      (quasiCoherentModuleProperty U).inverseImage (modulePullback a) :=
  sorry

/-- If `a` is an fppf hypercovering, then pushforward of modules along the spaces-étale
augmentation preserves quasi-coherence. -/
theorem modulePushforward_le_inverseImage (ha : IsFppfHypercovering a) :
    quasiCoherentModuleProperty U ≤
      (spacesQuasiCoherentModuleProperty X).inverseImage (modulePushforward a) :=
  sorry

namespace QCoh

/-- Restriction of `a^*` to quasi-coherent modules. -/
def pullback :
    (spacesQuasiCoherentModuleProperty X).FullSubcategory ⥤ QCoh U :=
  FullSubcategory.restrict (modulePullback a) (modulePullback_le_inverseImage a)

/-- The underlying module sheaf of `QCoh.pullback a` is module pullback along the
spaces-étale augmentation. -/
theorem pullback_obj (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory) :
    ((pullback a).obj F).obj = (modulePullback a).obj F.obj :=
  sorry

/-- Restriction of `a_*` to quasi-coherent modules, when `a` is an fppf hypercovering. -/
def pushforward (ha : IsFppfHypercovering a) :
    QCoh U ⥤ (spacesQuasiCoherentModuleProperty X).FullSubcategory :=
  FullSubcategory.restrict (modulePushforward a) (modulePushforward_le_inverseImage a ha)

/-- The underlying module sheaf of `QCoh.pushforward a ha` is module pushforward along
the spaces-étale augmentation. -/
theorem pushforward_obj (ha : IsFppfHypercovering a) (G : QCoh U) :
    ((pushforward a ha).obj G).obj = (modulePushforward a).obj G.obj :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
