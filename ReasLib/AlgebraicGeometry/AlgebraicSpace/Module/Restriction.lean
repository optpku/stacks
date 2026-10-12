/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Modules
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {W X : AlgebraicSpace S}

set_option maxHeartbeats 800000 in
/-- Identity maps on chart sections give a natural comparison of the structure presheaves
under representably étale postcomposition. -/
theorem restrictStructureMap_naturality (ι : W ⟶ X) (h_etale : Representable.Etale ι)
    {U V : (site W)ᵒᵖ} (map : U ⟶ V) :
    (structurePresheaf W).map map ≫ 𝟙 ((structurePresheaf W).obj V) =
      𝟙 ((structurePresheaf W).obj U) ≫
        (structurePresheaf X).map ((postcompose ι h_etale).op.map map) := sorry

/-- The structure-sheaf comparison for étale restriction is the identity on each chart's
ring of global sections. -/
def restrictStructureMap (ι : W ⟶ X) (h_etale : Representable.Etale ι) :
    structureSheaf W ⟶
      ((postcompose ι h_etale).sheafPushforwardContinuous RingCat.{u}
        (topology W) (topology X)).obj (structureSheaf X) :=
  ⟨{ app := fun _ => 𝟙 _
     naturality := fun _ _ map => restrictStructureMap_naturality ι h_etale map }⟩

/-- Restrict a module sheaf along a representably étale morphism by precomposing its
sections with chart postcomposition. -/
def restrict (ι : W ⟶ X) (h_etale : Representable.Etale ι) : Modules X ⥤ Modules W :=
  SheafOfModules.pushforward (restrictStructureMap ι h_etale)

/-- The underlying abelian presheaf of an étale restriction is precomposition with the
postcomposition functor on charts. -/
theorem restrict_apply (ι : W ⟶ X) (h_etale : Representable.Etale ι) (F : Modules X) :
    ((restrict ι h_etale).obj F).val.presheaf =
      (postcompose ι h_etale).op ⋙ F.val.presheaf := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
