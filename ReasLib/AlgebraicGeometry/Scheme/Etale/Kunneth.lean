/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale.Kunneth


/-- The first edge map in the chosen derived étale realization of the cartesian square. -/
noncomputable def leftLeg
    {P X S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
    [Abelian (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalCategory
      (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))]
    [MonoidalCategory
      (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))]
    (invP : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invF : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirF : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirC : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (adjF : invF ⊣ dirF)
    (modelC : CategoryTheory.Adjunction.TensorModel dirC
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))))
    (compF : modelC.left ≅ invF ⋙ invP)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    dirF.obj E ⟶ dirC.obj (invP.obj E) :=
  (modelC.adjunction.homEquiv (dirF.obj E) (invP.obj E))
    (compF.hom.app (dirF.obj E) ≫ invP.map (adjF.counit.app E))

/-- The second edge map in the chosen derived étale realization of the cartesian square. -/
noncomputable def rightLeg
    {P Y S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
    [Abelian (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalCategory
      (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))]
    [MonoidalCategory
      (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))]
    (invQ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invG : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirG : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirC : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (adjG : invG ⊣ dirG)
    (modelC : CategoryTheory.Adjunction.TensorModel dirC
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))))
    (compG : modelC.left ≅ invG ⋙ invQ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) :
    dirG.obj K ⟶ dirC.obj (invQ.obj K) :=
  (modelC.adjunction.homEquiv (dirG.obj K) (invQ.obj K))
    (compG.hom.app (dirG.obj K) ≫ invQ.map (adjG.counit.app K))

/-- The adjoint-side composite defining the chosen derived étale Künneth morphism. -/
noncomputable def adjointMap
    {P X Y S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
    [Abelian (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalCategory
      (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))]
    [MonoidalCategory
      (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))]
    (invP : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invQ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invF : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invG : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirF : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirG : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirC : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (adjF : invF ⊣ dirF) (adjG : invG ⊣ dirG)
    (modelC : CategoryTheory.Adjunction.TensorModel dirC
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))))
    (compF : modelC.left ≅ invF ⋙ invP) (compG : modelC.left ≅ invG ⋙ invQ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) :
    modelC.left.obj (dirF.obj E ⊗ dirG.obj K) ⟶ invP.obj E ⊗ invQ.obj K :=
  (modelC.comparison (dirF.obj E) (dirG.obj K)).hom ≫
    ((compF.hom.app (dirF.obj E) ≫ invP.map (adjF.counit.app E)) ⊗ₘ
      (compG.hom.app (dirG.obj K) ≫ invQ.map (adjG.counit.app K)))

/-- The Künneth morphism for a cartesian square in a chosen derived étale realization. -/
noncomputable def map
    {P X Y S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
    [Abelian (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalCategory
      (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))]
    [MonoidalCategory
      (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))]
    (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : P ⟶ S)
    (hcart : IsPullback p q f g) (hcF : c = p ≫ f) (hcG : c = q ≫ g)
    (invP : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invQ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invF : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invG : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirF : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirG : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirC : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (adjF : invF ⊣ dirF) (adjG : invG ⊣ dirG)
    (modelC : CategoryTheory.Adjunction.TensorModel dirC
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))))
    (compF : modelC.left ≅ invF ⋙ invP) (compG : modelC.left ≅ invG ⋙ invQ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) :
    dirF.obj E ⊗ dirG.obj K ⟶ dirC.obj (invP.obj E ⊗ invQ.obj K) :=
  (leftLeg invP invF dirF dirC adjF modelC compF E ⊗ₘ
      rightLeg invQ invG dirG dirC adjG modelC compG K) ≫
    modelC.adjunction.relativeDerivedCupProduct
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))))
      (fun A B ↦ (modelC.comparison A B).hom) (invP.obj E) (invQ.obj K)

/-- The Künneth morphism factors through its two named edge maps and the relative cup product. -/
theorem map_eq
    {P X Y S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
    [Abelian (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalCategory
      (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))]
    [MonoidalCategory
      (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))]
    (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : P ⟶ S)
    (hcart : IsPullback p q f g) (hcF : c = p ≫ f) (hcG : c = q ≫ g)
    (invP : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invQ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invF : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invG : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirF : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirG : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirC : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (adjF : invF ⊣ dirF) (adjG : invG ⊣ dirG)
    (modelC : CategoryTheory.Adjunction.TensorModel dirC
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))))
    (compF : modelC.left ≅ invF ⋙ invP) (compG : modelC.left ≅ invG ⋙ invQ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) :
    map p q f g c hcart hcF hcG invP invQ invF invG dirF dirG dirC
        adjF adjG modelC compF compG E K =
      (leftLeg invP invF dirF dirC adjF modelC compF E ⊗ₘ
        rightLeg invQ invG dirG dirC adjG modelC compG K) ≫
        modelC.adjunction.relativeDerivedCupProduct
          (MonoidalCategory.tensoringLeft
            (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
          (MonoidalCategory.tensoringLeft
            (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))))
          (fun A B ↦ (modelC.comparison A B).hom) (invP.obj E) (invQ.obj K) := sorry

/-- The transpose of the Künneth morphism is the adjoint-side composite from the remark. -/
theorem map_adjoint_spec
    {P X Y S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
    [Abelian (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalCategory
      (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))]
    [MonoidalCategory
      (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))]
    (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : P ⟶ S)
    (hcart : IsPullback p q f g) (hcF : c = p ≫ f) (hcG : c = q ≫ g)
    (invP : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invQ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invF : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (invG : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirF : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirG : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (dirC : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ)))
    (adjF : invF ⊣ dirF) (adjG : invG ⊣ dirG)
    (modelC : CategoryTheory.Adjunction.TensorModel dirC
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{v} Λ))))
      (MonoidalCategory.tensoringLeft
        (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{v} Λ)))))
    (compF : modelC.left ≅ invF ⋙ invP) (compG : modelC.left ≅ invG ⋙ invQ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) :
    (modelC.adjunction.homEquiv
      (dirF.obj E ⊗ dirG.obj K) (invP.obj E ⊗ invQ.obj K)).symm
        (map p q f g c hcart hcF hcG invP invQ invF invG dirF dirG dirC
          adjF adjG modelC compF compG E K) =
      adjointMap invP invQ invF invG dirF dirG dirC adjF adjG modelC compF compG E K := sorry

end AlgebraicGeometry.Scheme.Etale.Kunneth

end
