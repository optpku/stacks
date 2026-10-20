module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.TautologicalDescent

/-! The actual projectivization base-change map, on quotient classes. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.InvertibleQuotient
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveBaseChange
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (E : X.Modules) [E.IsQuasicoherent] (g : Y ⟶ X)

instance pulled_qc : ((Modules.pullback g).obj E).IsQuasicoherent :=
  Modules.pullback_quasiCoherentModuleProperty g inferInstance

theorem basePoint_comp (T : Over S) (p : SmallProjectiveFunctor.Point ((Modules.pullback g).obj E) T) :
    SmallProjectiveFunctor.homOfPoint p.1 ≫ g =
      SmallProjectiveFunctor.homOfPoint (g.app (op T) p.1) := by sorry

def pointMap (T : Over S) (p : SmallProjectiveFunctor.Point ((Modules.pullback g).obj E) T) :
    SmallProjectiveFunctor.Point E T :=
  ⟨g.app (op T) p.1,
    (basePoint_comp E g T p) ▸
      SmallProjectiveFunctor.pointEquiv E T (SmallProjectiveFunctor.homOfPoint p.1 ≫ g)
        (precomposeIsoClass ((Modules.pullbackCompIso (SmallProjectiveFunctor.homOfPoint p.1) g).app E).symm
          ((SmallProjectiveFunctor.pointEquiv ((Modules.pullback g).obj E) T
            (SmallProjectiveFunctor.homOfPoint p.1)).symm p.2))⟩

theorem pointMap_natural {T U : Over S} (a : U ⟶ T)
    (p : SmallProjectiveFunctor.Point ((Modules.pullback g).obj E) T) :
    SmallProjectiveFunctor.map E a (pointMap E g T p) =
      pointMap E g U (SmallProjectiveFunctor.map ((Modules.pullback g).obj E) a p) := by sorry

def map : ProjectiveAtlas.space ((Modules.pullback g).obj E) ⟶ ProjectiveAtlas.space E where
  app T := TypeCat.ofHom (pointMap E g T.unop)
  naturality T U a := by
    ext p
    exact (pointMap_natural E g a.unop p).symm

theorem map_projection : map E g ≫ ProjectiveAtlas.projection E =
    ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g := rfl

/-- Every quotient of h*(g*E) is exactly a quotient of (h≫g)*E via the specified
composition iso; the base-change square therefore has its actual universal property. -/
theorem isPullback : IsPullback (map E g) (ProjectiveAtlas.projection ((Modules.pullback g).obj E))
    (ProjectiveAtlas.projection E) g := by sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveBaseChange
