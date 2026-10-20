module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImage.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

section ExactAb

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.36.2 (1): the inverse-image functor on abelian sheaves for the small
étale sites is exact. -/
@[stacks 03Q1] #check
  (AlgebraicGeometry.Scheme.smallEtaleInverseImage_exact_addCommGrp f :
    exactFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
      ((Scheme.smallEtalePullback f).sheafPullback AddCommGrpCat.{w}
        Y.smallEtaleTopology X.smallEtaleTopology))

end ExactAb

section ExactType

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type v)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type v,
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.36.2 (2): the inverse-image functor on sheaves of sets for the small
étale sites is exact, i.e. it preserves finite limits and finite colimits, see
Categories, Definition 4.23.1. -/
@[stacks 03Q1] #check
  (AlgebraicGeometry.Scheme.smallEtaleInverseImage_exact_type f :
    exactFunctor (Sheaf Y.smallEtaleTopology (Type v))
      (Sheaf X.smallEtaleTopology (Type v))
      ((Scheme.smallEtalePullback f).sheafPullback (Type v)
        Y.smallEtaleTopology X.smallEtaleTopology))

end ExactType

section Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u,
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable (xbar : Scheme.GeometricPoint X)
variable (G : Sheaf Y.smallEtaleTopology (Type u))

/- Lemma 59.36.2 (3): there is a canonical identification
`(f⁻¹ G)_x̄ ≅ G_ȳ` where `ȳ = f ∘ x̄`. -/
@[stacks 03Q1] #check
  (AlgebraicGeometry.Scheme.smallEtaleInverseImage_stalkIso f xbar G :
    (Scheme.GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
      (((Scheme.smallEtalePullback f).sheafPullback (Type u)
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) ≅
      (Scheme.GeometricPoint.toSmallEtalePoint
        (Scheme.smallEtaleInverseImage_imagePoint f xbar)).sheafFiber.obj G)

end Stalk

section Representable

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type (max w (u + 1)))]
variable [HasWeakSheafify Y.smallEtaleTopology (Type (max w (u + 1)))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type (max w (u + 1)),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable (V : Y.Etale)

/- Lemma 59.36.2 (4): for `V → Y` étale one has `f⁻¹ h_V = h_{X ×_Y V}`. -/
@[stacks 03Q1] #check
  (AlgebraicGeometry.Scheme.smallEtaleInverseImage_representableIso f V :
    ((Scheme.smallEtalePullback f).sheafPullback (Type (max w (u + 1)))
      Y.smallEtaleTopology X.smallEtaleTopology).obj
        (Y.smallEtaleTopology.uliftSheafifiedRepresentable.{max w (u + 1), u, u + 1} V) ≅
      X.smallEtaleTopology.uliftSheafifiedRepresentable.{max w (u + 1), u, u + 1}
        ((Scheme.smallEtalePullback f).obj V))

end Representable
