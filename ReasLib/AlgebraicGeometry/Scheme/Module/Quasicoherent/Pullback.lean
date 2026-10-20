module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along a morphism of schemes preserves quasicoherence of module sheaves. -/
instance pullback_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    [F.IsQuasicoherent] : ((pullback f).obj F).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.QCoh

/-- Quasi-coherence as an object property on the fibres of the module-sheaf
pseudofunctor. -/
def descentObjectProperty : Modules.descentPseudofunctor.ObjectProperty where
  prop X := Scheme.quasiCoherentModuleProperty X.as.unop

/-- Pullback of module sheaves preserves the fibrewise quasi-coherence property. -/
instance descentObjectPropertyIsClosedUnderMapObj :
    descentObjectProperty.IsClosedUnderMapObj := sorry

/-- The contravariant pseudofunctor sending a scheme to its category of quasi-coherent
modules and a scheme morphism to pullback. -/
noncomputable def pseudofunctor :
    LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat :=
  descentObjectProperty.fullsubcategory

/-- Pullback of quasi-coherent modules along a scheme morphism. -/
noncomputable def pullback {X Y : Scheme.{u}} (g : Y ⟶ X) : QCoh X ⥤ QCoh Y :=
  (pseudofunctor.map g.op.toLoc).toFunctor

/-- The underlying module sheaf of a pulled-back quasi-coherent module is the usual
module pullback. -/
theorem pullback_obj {X Y : Scheme.{u}} (g : Y ⟶ X) (F : QCoh X) :
    ((pullback g).obj F).obj = (Modules.pullback g).obj F.obj := sorry

/-- The underlying map of a pulled-back morphism is the usual module-pullback map. -/
theorem pullback_map {X Y : Scheme.{u}} (g : Y ⟶ X) {F G : QCoh X} (a : F ⟶ G) :
    ((pullback g).map a).hom = (Modules.pullback g).map a.hom := sorry

/-- The fibre of the quasi-coherent-module pseudofunctor at `X` is `QCoh X`. -/
theorem pseudofunctor_obj (X : Scheme.{u}) :
    pseudofunctor.obj (.mk (.op X)) = Cat.of (QCoh X) := sorry

/-- The action of the quasi-coherent-module pseudofunctor is pullback. -/
theorem pseudofunctor_map {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pseudofunctor.map g.op.toLoc).toFunctor = pullback g := sorry

end AlgebraicGeometry.Scheme.QCoh
