module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Sheafification
public import Mathlib.CategoryTheory.Whiskering

/-!
# Concrete maps out of Type-u big étale sheafification

The big étale sheafification evaluates a small-site sheafification at the
identity chart of each test scheme. Applying the actual local sheafification
lift at that chart constructs its map into a given big étale sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheafification

variable {S : Scheme.{u}}

/-- A big étale sheaf restricts to a sheaf on each test scheme's small étale site. -/
theorem restriction_isSheaf (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (T : Over S) :
    Presheaf.IsSheaf T.left.smallEtaleTopology (restriction G.obj T) := sorry

/-- The identity-on-schemes arrow from a test scheme to its identity étale chart over S. -/
def toIdentityChart (T : Over S) :
    T ⟶ ((Scheme.Etale.forget T.left) ⋙ Over.map T.hom).obj
      (Scheme.Etale.mk (𝟙 T.left)) :=
  Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ (𝟙 T.left ≫ T.hom) = T.hom
    simp)

/-- Extend the supplied presheaf map by actual small-site sheafification on each test scheme. -/
def lift {F : (Over S)ᵒᵖ ⥤ Type u}
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj) :
    sheafify F ⟶ G.obj where
  app T :=
    (sheafifyLift T.unop.left.smallEtaleTopology
      (Functor.whiskerLeft ((Scheme.Etale.forget T.unop.left) ⋙ Over.map T.unop.hom).op η)
      (restriction_isSheaf G T.unop)).app
        (op (Scheme.Etale.mk (𝟙 T.unop.left))) ≫
      G.obj.map (toIdentityChart T.unop).op
  naturality := sorry

/-- The constructed lift extends the supplied presheaf map along the original sheafification unit. -/
theorem toSheafify_lift {F : (Over S)ᵒᵖ ⥤ Type u}
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj) :
    toSheafify F ≫ lift G η = η := sorry

/-- Sheafification extension is determined by its values on the original presheaf. -/
theorem lift_unique {F : (Over S)ᵒᵖ ⥤ Type u}
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj)
    (θ : sheafify F ⟶ G.obj) (hθ : toSheafify F ≫ θ = η) : θ = lift G η := sorry

end AlgebraicGeometry.Scheme.EtaleSheafification
