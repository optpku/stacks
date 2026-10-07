module

import ReasLib.AlgebraicGeometry.Scheme.Etale.Kunneth
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/- Remark 59.97.1: for a cartesian square of schemes and a chosen compatible realization of the
derived étale inverse and direct images, the Künneth morphism has source
`Rf_* E ⊗ Rg_* K` and target `Rc_* (p⁻¹ E ⊗ q⁻¹ K)`, and is obtained from the two counits and
the relative cup product. -/
@[stacks 0F1E] #check
  (AlgebraicGeometry.Scheme.Etale.Kunneth.map :
    ∀ {P X Y S : Scheme.{u}} {Λ : Type v} [CommRing Λ]
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
      (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))),
      dirF.obj E ⊗ dirG.obj K ⟶ dirC.obj (invP.obj E ⊗ invQ.obj K))

#check AlgebraicGeometry.Scheme.Etale.Kunneth.leftLeg
#check AlgebraicGeometry.Scheme.Etale.Kunneth.rightLeg
#check AlgebraicGeometry.Scheme.Etale.Kunneth.adjointMap
#check AlgebraicGeometry.Scheme.Etale.Kunneth.map_eq
#check AlgebraicGeometry.Scheme.Etale.Kunneth.map_adjoint_spec

end AlgebraicGeometry.Scheme

end
