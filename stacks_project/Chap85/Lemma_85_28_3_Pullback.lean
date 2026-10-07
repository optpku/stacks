module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap85.Lemma_85_28_1
public import stacks_project.Chap85.Lemma_85_28_1_Pullback
public import stacks_project.Chap85.Lemma_85_28_4_QCoh

/-!
# Quasi-coherent pullback along a morphism of simplicial schemes

Restriction of `modulePullback` to the full subcategory of quasi-coherent
modules on the Zariski ringed site of a simplicial scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

namespace QCoh

namespace pullback

/-- Pullback of module sheaves along a morphism of simplicial schemes carries
quasi-coherent modules to quasi-coherent modules. -/
theorem mapsTo {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    quasiCoherentModuleProperty U ≤
      (quasiCoherentModuleProperty V).inverseImage (modulePullback f) :=
  sorry

end pullback

/-- Pullback of quasi-coherent modules along a morphism of simplicial schemes. -/
noncomputable def pullback {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    QCoh U ⥤ QCoh V :=
  FullSubcategory.restrict (modulePullback f) (pullback.mapsTo f)

/-- The underlying module sheaf of a pulled-back quasi-coherent module is the
usual module pullback. -/
theorem pullback_obj {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (F : QCoh U) :
    ((pullback f).obj F).obj = (modulePullback f).obj F.obj :=
  sorry

/-- Forgetting quasi-coherence after restricted pullback recovers ambient
module-sheaf pullback. -/
noncomputable def pullback.inclusionIso {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) :
    pullback f ⋙ inclusion V ≅ inclusion U ⋙ modulePullback f :=
  FullSubcategory.restrict.compιIso (modulePullback f) (pullback.mapsTo f)

end QCoh

end AlgebraicGeometry.SimplicialObject
